#!/usr/bin/env python3
"""
lc_lookup_service.py - small local service for the Koha "AI CATALOGUING" button.

WHAT IT DOES
    Your browser cannot read the Library of Congress catalogue directly. This service runs
    on the Koha server, asks the Library of Congress (SRU, MARCXML) for an ISBN, and returns
    the cataloguer's own MARC fields as JSON, exactly as the Library of Congress published them.
    Nothing is guessed, completed or rewritten here.

    ORDER OF SEARCH (stops at the first record found)
      1. Library of Congress by ISBN (13- and 10-digit forms)
      2. Library of Congress by LCCN: the LCCN is looked up from HathiTrust and Open Library
         (they answer by ISBN), then the Library of Congress record with that number is read
      3. Other national / university libraries (SRU, MARCXML): Library Hub Discover (UK), DNB (Germany)
    A record from steps 1 and 3 is returned ONLY if the record itself lists the ISBN asked for.
    A record from step 2 is marked "match": "lccn" so the Koha button can tell the cataloguer to check.
    No match anywhere = {"found": false}. The Koha button then falls back to Open Library /
    Google Books and marks every value orange.

USAGE
    python3 lc_lookup_service.py                # listens on 127.0.0.1:8099 (this server only)
    curl "http://127.0.0.1:8099/lookup?isbn=9780131103627"
    curl  http://127.0.0.1:8099/health

SETTINGS (environment variables, all optional)
    LC_SERVICE_HOST    default 127.0.0.1   (keep it local; Apache passes requests to it)
    LC_SERVICE_PORT    default 8099
    LC_ALLOW_ORIGIN    default empty       (only needed if the browser calls the service directly)

Needs only Python 3.8+ (standard library) and internet access from the server.
"""
import json
import os
import re
import threading
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HOST = os.environ.get("LC_SERVICE_HOST", "127.0.0.1")
PORT = int(os.environ.get("LC_SERVICE_PORT", "8099"))
ALLOW_ORIGIN = os.environ.get("LC_ALLOW_ORIGIN", "")

LC_NAME = "Library of Congress"
LC_SRU = ("https://lx2.loc.gov/sru/lcdb?operation=searchRetrieve&version=1.1"
          "&query={query}&maximumRecords=5&recordSchema=marcxml")
LC_PERMALINK = "https://lccn.loc.gov/{lccn}/marcxml"
HATHI_URL = "https://catalog.hathitrust.org/api/volumes/brief/isbn/{isbn}.json"
OPENLIB_URL = "https://openlibrary.org/api/books?bibkeys=ISBN:{isbn}&format=json&jscmd=data"

# Other libraries, searched only when the Library of Congress has nothing.
# (name, url template, query template). A failing or unreachable source is skipped quietly.
# To add a library: add one line here. The record is accepted only if it lists our ISBN.
OTHER_SOURCES = [
    ("Library Hub Discover (UK)",
     "https://discover.libraryhub.jisc.ac.uk/sru-api?version=1.1&operation=searchRetrieve"
     "&query={query}&maximumRecords=5&recordSchema=marcxml", "bath.isbn={isbn}"),
    ("Deutsche Nationalbibliothek",
     "https://services.dnb.de/sru/dnb?version=1.1&operation=searchRetrieve"
     "&query={query}&maximumRecords=5&recordSchema=MARC21-xml", "num={isbn}"),
]

TOTAL_SECONDS = 55          # give up on the whole search after this long

# MARC tags handed to the Koha form (everything the AI CATALOGUING button can use)
WANTED = {
    "010", "020", "050", "082", "100", "110", "111", "245", "250", "260", "264",
    "300", "490", "500", "504", "520", "650", "651", "700", "710", "711", "830",
}

HIT_SECONDS = 24 * 3600     # remember found records for a day
MISS_SECONDS = 3600         # remember "not found" for an hour
MIN_GAP_SECONDS = 1.0       # be polite: pause between calls to the same server

_cache = {}
_cache_lock = threading.Lock()
_upstream_lock = threading.Lock()
_last_call = {}


# ----------------------------------------------------------------------------
# ISBN handling
# ----------------------------------------------------------------------------
def clean(s):
    return re.sub(r"[^0-9Xx]", "", s or "").upper()


def to_isbn13(raw):
    """Valid ISBN-13 string, or None if the number is not a valid ISBN."""
    s = clean(raw)
    if len(s) == 10:
        total = sum((10 if c == "X" else int(c)) * (10 - i) for i, c in enumerate(s))
        if total % 11 != 0:
            return None
        base = "978" + s[:9]
        check = (10 - sum(int(c) * (3 if i % 2 else 1) for i, c in enumerate(base)) % 10) % 10
        return base + str(check)
    if len(s) == 13 and s.isdigit():
        total = sum(int(c) * (3 if i % 2 else 1) for i, c in enumerate(s))
        return s if total % 10 == 0 else None
    return None


def to_isbn10(isbn13):
    if not isbn13.startswith("978"):
        return None
    body = isbn13[3:12]
    total = sum(int(c) * (10 - i) for i, c in enumerate(body))
    check = (11 - total % 11) % 11
    return body + ("X" if check == 10 else str(check))


# ----------------------------------------------------------------------------
# MARCXML -> JSON   (works with or without the MARC21 namespace)
# ----------------------------------------------------------------------------
def local(tag):
    return tag.rsplit("}", 1)[-1] if isinstance(tag, str) else ""


def children(el, name):
    return [c for c in el if local(c.tag) == name]


def marc_records(xml_bytes):
    root = ET.fromstring(xml_bytes)
    return [e for e in root.iter() if local(e.tag) == "record" and children(e, "datafield")]


def datafields(rec, tag):
    return [d for d in children(rec, "datafield") if d.get("tag") == tag]


def record_isbns(rec):
    """ISBNs a record claims (020$a only; $z = cancelled/invalid, never matched)."""
    found = set()
    for df in datafields(rec, "020"):
        for sf in children(df, "subfield"):
            if sf.get("code") != "a":
                continue
            parts = (sf.text or "").split()
            if not parts:
                continue
            token = clean(parts[0])
            if len(token) == 13:
                found.add(token)
            elif len(token) == 10:
                found.add(token)
                v13 = to_isbn13(token)
                if v13:
                    found.add(v13)
    return found


def normalize_lccn(raw):
    """LCCN in the form the Library of Congress searches on (no spaces/hyphens, 6-digit serial), or None."""
    s = re.sub(r"\s+", "", raw or "").lower()
    if "/" in s:                       # '90012390 //r91' style suffix
        s = s.split("/")[0]
    if "-" in s:
        left, _, right = s.partition("-")
        if not right.isdigit():
            return None
        s = left + right.zfill(6)
    return s if re.fullmatch(r"[a-z]{0,3}(\d{2}|\d{4})\d{6}", s) else None


def record_lccn(rec):
    for df in datafields(rec, "010"):
        for sf in children(df, "subfield"):
            if sf.get("code") == "a":
                n = normalize_lccn(sf.text or "")
                if n:
                    return n
    return None


def record_to_json(rec, isbn13, source_name, extra=None):
    control = ""
    for cf in children(rec, "controlfield"):
        if cf.get("tag") == "001":
            control = (cf.text or "").strip()
    fields = {}
    for df in children(rec, "datafield"):
        tag = df.get("tag")
        if tag not in WANTED:
            continue
        seq, sub = [], {}
        for sf in children(df, "subfield"):
            code, value = sf.get("code"), (sf.text or "").strip()
            if not value:
                continue
            seq.append([code, value])
            sub.setdefault(code, []).append(value)
        fields.setdefault(tag, []).append(
            {"ind1": df.get("ind1") or " ", "ind2": df.get("ind2") or " ", "sub": sub, "seq": seq}
        )
    out = {
        "found": True,
        "source": source_name,
        "control_number": control,
        "isbn": isbn13,
        "match": "isbn",
        "fields": fields,
    }
    if extra:
        out.update(extra)
    return out


# ----------------------------------------------------------------------------
# Network (separate function so it can be replaced in tests)
# ----------------------------------------------------------------------------
def fetch_upstream(url, timeout=20):
    host = urllib.parse.urlparse(url).netloc
    with _upstream_lock:
        wait = MIN_GAP_SECONDS - (time.time() - _last_call.get(host, 0.0))
        if wait > 0:
            time.sleep(wait)
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "KNUST-Koha-lc-lookup/2.0"})
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.read()
        finally:
            _last_call[host] = time.time()


class Search:
    """One lookup: keeps the clock, remembers what was tried, tells whether any server answered."""

    def __init__(self):
        self.started = time.time()
        self.tried = []
        self.answered = False

    def time_left(self):
        return TOTAL_SECONDS - (time.time() - self.started)

    def get(self, url):
        """bytes, or None when the call failed (reason is noted)."""
        if self.time_left() <= 0:
            return None
        try:
            data = fetch_upstream(url)
            self.answered = True
            return data
        except Exception:
            return None

    def note(self, text):
        self.tried.append(text)


def sru_records(search, template, query):
    data = search.get(template.format(query=urllib.parse.quote(query, safe="")))
    if data is None:
        return None
    try:
        return marc_records(data)
    except ET.ParseError:
        return None


def find_in_sru(search, name, template, query_templates, variants, wanted, isbn13):
    """Record that lists our ISBN, from one SRU server. None if none (or the server failed)."""
    failed = 0
    for variant in variants:
        for qt in query_templates:
            recs = sru_records(search, template, qt.format(isbn=variant))
            if recs is None:
                failed += 1
                continue
            for rec in recs:
                if record_isbns(rec) & wanted:
                    return record_to_json(rec, isbn13, name)
    search.note("%s: %s" % (name, "not reachable" if failed and failed == len(variants) * len(query_templates)
                            else "no record for this ISBN"))
    return None


def lccns_for(search, isbn13, variants):
    """LCCNs that HathiTrust / Open Library list for this ISBN (they answer by ISBN)."""
    found = []

    def add(raw):
        n = normalize_lccn(str(raw))
        if n and n not in found:
            found.append(n)

    data = search.get(HATHI_URL.format(isbn=isbn13))
    if data:
        try:
            for rec in (json.loads(data).get("records") or {}).values():
                for v in rec.get("lccns") or []:
                    add(v)
        except (ValueError, AttributeError):
            pass
    data = search.get(OPENLIB_URL.format(isbn=isbn13))
    if data:
        try:
            entry = json.loads(data).get("ISBN:" + isbn13) or {}
            for v in (entry.get("identifiers") or {}).get("lccn") or []:
                add(v)
        except (ValueError, AttributeError):
            pass
    return found


def find_by_lccn(search, lccn, isbn13, wanted):
    """The Library of Congress record with this LCCN (permalink first, SRU second)."""
    recs = None
    data = search.get(LC_PERMALINK.format(lccn=lccn))
    if data:
        try:
            recs = marc_records(data)
        except ET.ParseError:
            recs = None
    if not recs:
        recs = sru_records(search, LC_SRU, "bath.lccn=" + lccn)
    for rec in recs or []:
        rl = record_lccn(rec)
        if rl and rl != lccn:
            continue                      # a different record: never use it
        isbns = sorted(record_isbns(rec))
        out = record_to_json(rec, isbn13, LC_NAME, {
            "match": "isbn" if (set(isbns) & wanted) else "lccn",
            "lccn": lccn,
            "record_isbns": isbns,
        })
        return out
    return None


def lookup(isbn13):
    """Dict for the browser. Raises only when no upstream server could be reached at all."""
    now = time.time()
    with _cache_lock:
        hit = _cache.get(isbn13)
        if hit and hit[0] > now:
            return hit[1]

    variants = [isbn13] + ([to_isbn10(isbn13)] if to_isbn10(isbn13) else [])
    wanted = set(variants)
    search = Search()
    result = None

    # 1) Library of Congress by ISBN
    result = find_in_sru(search, LC_NAME, LC_SRU, ["bath.isbn=^{isbn}", "bath.isbn={isbn}"], variants, wanted, isbn13)

    # 2) Library of Congress by LCCN (number supplied by HathiTrust / Open Library)
    if not result:
        lccns = lccns_for(search, isbn13, variants)
        for lccn in lccns[:3]:
            result = find_by_lccn(search, lccn, isbn13, wanted)
            if result:
                break
        search.note("Library of Congress by LCCN: " + (
            ("found via LCCN " + result["lccn"]) if result
            else ("no record for LCCN " + ", ".join(lccns[:3])) if lccns else "no LCCN known for this ISBN"))

    # 3) other libraries
    if not result:
        for name, template, qt in OTHER_SOURCES:
            result = find_in_sru(search, name, template, [qt], variants, wanted, isbn13)
            if result:
                break

    if not result:
        if not search.answered:
            raise RuntimeError("no catalogue server could be reached")
        result = {"found": False, "isbn": isbn13}
    result["tried"] = search.tried

    ttl = HIT_SECONDS if result["found"] else MISS_SECONDS
    with _cache_lock:
        _cache[isbn13] = (now + ttl, result)
    return result


# ----------------------------------------------------------------------------
# HTTP
# ----------------------------------------------------------------------------
class Handler(BaseHTTPRequestHandler):
    server_version = "LCLookup/2.0"

    def _send(self, status, payload, content_type="application/json; charset=utf-8"):
        body = payload if isinstance(payload, bytes) else json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        if ALLOW_ORIGIN:
            self.send_header("Access-Control-Allow-Origin", ALLOW_ORIGIN)
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        parsed = urllib.parse.urlparse(self.path)
        if parsed.path == "/health":
            return self._send(200, b"ok", "text/plain; charset=utf-8")
        if parsed.path == "/lookup":
            raw = (urllib.parse.parse_qs(parsed.query).get("isbn") or [""])[0]
            isbn13 = to_isbn13(raw)
            if not isbn13:
                return self._send(400, {"found": False, "error": "invalid ISBN"})
            try:
                return self._send(200, lookup(isbn13))
            except Exception as exc:  # upstream unreachable or unreadable
                return self._send(502, {"found": False, "error": "upstream error: %s" % exc})
        return self._send(404, {"error": "not found"})

    def log_message(self, fmt, *args):
        print("%s - %s" % (self.address_string(), fmt % args), flush=True)


def main():
    server = ThreadingHTTPServer((HOST, PORT), Handler)
    print("LC lookup service listening on http://%s:%d" % (HOST, PORT), flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
