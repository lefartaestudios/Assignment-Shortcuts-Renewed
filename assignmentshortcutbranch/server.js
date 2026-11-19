// Assignment Shortcuts / About:NotBlank: proxy server. Node 18+, no dependencies.
//
//   node server.js            -> http://localhost:3000
//
// Environment variables (all optional):
//   PORT             port to listen on (default 3000)
//   PUBLIC_URL       this server's public address, if it sits behind a reverse proxy
//   ALLOWED_ORIGINS  comma-separated list of sites allowed to call /proxy from a browser
//                    (default "*", which lets any site use it; set this when you deploy)
//   RATE_LIMIT       requests per minute per visitor (default 120)
//   MAX_CONCURRENT   simultaneous upstream requests across all visitors (default 100)
//   MAX_PER_CLIENT   simultaneous upstream requests per visitor (default 10)
//   TRUST_PROXY      set to 1 to read the visitor's address from X-Forwarded-For
//   SESSION_HOURS    how long a visitor's saved logins are kept after their last request
//                    (default 12)
//
// Endpoints
//   GET /proxy?url=<address>[&sid=<session>]
//       The page or file exactly as the site sent it, with CORS headers and an
//       X-Final-URL header holding the address after redirects. index.html uses this
//       when PROXY_URL points at this server. POST/PUT/PATCH bodies are passed through
//       untouched, which is what makes signing in work.
//   GET /proxy?mode=browse&url=<address>[&sid=<session>]
//       Same, but HTML also gets a script that sends the page's own fetch/XHR calls back
//       through the proxy. Used by the "Show in frame" button.
//   GET /proxy?mode=module&url=<address>[&sid=<session>]
//       A JavaScript file with its import statements pointed back through the proxy, so
//       ES modules (used by most modern sites) load. index.html asks for this itself.
//   GET /session    what this visitor has signed in to (never returns cookie values)
//   DELETE /session forget every saved login for this visitor (sign out of everything)
//   GET /health     returns "ok"
//   GET /           serves index.html (and /favicon.ico) from this folder
//
// Signing in
//   A site signs someone in by handing out cookies. The browser here only ever talks to
//   the proxy, so the proxy keeps those cookies itself: one jar per visitor, per site,
//   held in memory. Every request the proxy makes carries the cookies that site handed
//   out, and every Set-Cookie it sends back updates the jar (and never reaches the
//   visitor's browser, so the real site's cookies never leave this server).
const http = require("http");
const fs = require("fs");
const path = require("path");
const crypto = require("crypto");
const dns = require("dns").promises;
const net = require("net");

const PORT = process.env.PORT || 3000;
const PUBLIC_URL = process.env.PUBLIC_URL;
const ALLOWED = (process.env.ALLOWED_ORIGINS || "*").split(",").map((s) => s.trim()).filter(Boolean);
const RATE_LIMIT = Number(process.env.RATE_LIMIT) || 120;
const MAX_CONCURRENT = Math.max(1, Number(process.env.MAX_CONCURRENT) || 100);
const MAX_PER_CLIENT = Math.max(1, Number(process.env.MAX_PER_CLIENT) || 10);
const TRUST_PROXY = process.env.TRUST_PROXY === "1";
const SESSION_HOURS = Math.max(1, Number(process.env.SESSION_HOURS) || 12);

const MAX_REDIRECTS = 8;
const TIMEOUT_MS = 90000;
// Binary/passthrough responses (images, video, fonts, plain scripts, ...) are streamed
// straight through rather than held in memory, so this can be generous. Only HTML
// (browse mode) and JS modules need their full text buffered to rewrite it, so those get
// their own, smaller cap further down.
const MAX_BYTES = 250 * 1024 * 1024;
const MAX_TEXT_BYTES = 60 * 1024 * 1024;
const REQUEST_MAX_BYTES = 25 * 1024 * 1024; // data the visitor's own page sends up (POSTs)
const DEFAULT_UA = "Mozilla/5.0 (compatible; AssignmentShortcuts/2.1)";

// Headers that must not be passed on: they would block framing, tie the response to the
// proxy's own connection, or leak CORS rules from the real site. Note that set-cookie is
// handled by hand (see "Signing in" below) rather than forwarded blindly.
const STRIP = new Set(["content-security-policy", "content-security-policy-report-only", "x-frame-options",
  "content-encoding", "content-length", "transfer-encoding", "connection", "keep-alive", "set-cookie",
  "strict-transport-security", "cross-origin-opener-policy", "cross-origin-embedder-policy",
  "cross-origin-resource-policy", "access-control-allow-origin", "access-control-allow-credentials",
  "access-control-allow-methods", "access-control-allow-headers", "access-control-expose-headers"]);

// Request headers that are passed on to the site, so sign-in forms and token checks see
// what the visitor's browser really sent.
const FORWARD_REQUEST_HEADERS = ["user-agent", "accept", "accept-language", "content-type", "range",
  "authorization", "x-requested-with", "x-csrf-token", "x-xsrf-token", "accept-encoding"];

// ---- Visitors: a simple per-address rate limit ----
const hits = new Map();
const activeByClient = new Map();
let activeRequests = 0;

function clientKey(req) {
  const fwd = TRUST_PROXY ? String(req.headers["x-forwarded-for"] || "").split(",")[0].trim() : "";
  return fwd || req.socket.remoteAddress || "?";
}
function limited(req) {
  const who = clientKey(req);
  const now = Date.now();
  let h = hits.get(who);
  if (!h || now > h.reset) { h = { n: 0, reset: now + 60000 }; hits.set(who, h); }
  h.n++;
  return h.n > RATE_LIMIT;
}
setInterval(() => { const now = Date.now(); for (const [k, v] of hits) if (now > v.reset) hits.delete(k); }, 60000).unref();

// ---- SSRF protection: never let the proxy reach private or internal addresses ----
function isPrivateIp(ip) {
  if (net.isIPv4(ip)) {
    const [a, b] = ip.split(".").map(Number);
    return a === 0 || a === 10 || a === 127 || (a === 169 && b === 254) || (a === 172 && b >= 16 && b <= 31) ||
      (a === 192 && b === 168) || (a === 100 && b >= 64 && b <= 127) || a >= 224;
  }
  const l = ip.toLowerCase();
  if (l === "::1" || l === "::" || l.startsWith("fc") || l.startsWith("fd") || l.startsWith("fe80")) return true;
  if (l.startsWith("::ffff:")) return isPrivateIp(l.slice(7));
  return false;
}
async function assertPublic(u) {
  if (!/^https?:$/.test(u.protocol)) throw new Error("Only http and https addresses are allowed");
  const host = u.hostname.replace(/^\[|\]$/g, "");
  const addrs = net.isIP(host) ? [{ address: host }] : await dns.lookup(host, { all: true });
  for (const a of addrs) if (isPrivateIp(a.address)) throw new Error("That address is not allowed");
}

// ============================================================================
// Signing in: sessions and cookie jars
// ============================================================================
const SID_PARAM = "sid";
const SID_COOKIE = "nb_sid";
const SID_HEADER = "x-nb-session";
const SID_RE = /^[A-Za-z0-9._-]{8,64}$/;
const MAX_COOKIES_PER_SITE = 300;

// sid -> { seen: ms, jars: Map(host -> Map(path|name -> cookie)) }
const sessions = new Map();

function newSid() {
  return crypto.randomBytes(18).toString("base64url");
}

function isHttps(req) {
  const proto = String(req.headers["x-forwarded-proto"] || "").split(",")[0].trim().toLowerCase();
  if (proto) return proto === "https";
  if (PUBLIC_URL) return PUBLIC_URL.startsWith("https:");
  return Boolean(req.socket && req.socket.encrypted);
}

function cookiePairs(header) {
  const out = [];
  for (const part of String(header || "").split(";")) {
    const i = part.indexOf("=");
    if (i < 1) continue;
    const name = part.slice(0, i).trim();
    if (!name) continue;
    out.push([name, part.slice(i + 1).trim()]);
  }
  return out;
}

// "name=value; Path=/; HttpOnly; SameSite=None" -> a cookie record.
function parseSetCookie(line) {
  const bits = String(line || "").split(";");
  const first = bits.shift() || "";
  const eq = first.indexOf("=");
  if (eq < 1) return null;
  const c = { name: first.slice(0, eq).trim(), value: first.slice(eq + 1).trim(),
    domain: "", path: "/", expires: 0, secure: false, httpOnly: false, sameSite: "" };
  for (const b of bits) {
    const i = b.indexOf("=");
    const k = (i < 0 ? b : b.slice(0, i)).trim().toLowerCase();
    const v = i < 0 ? "" : b.slice(i + 1).trim();
    if (k === "domain" && v) c.domain = v.replace(/^\./, "").toLowerCase();
    else if (k === "path" && v) c.path = v.startsWith("/") ? v : "/";
    else if (k === "expires") { const t = Date.parse(v); if (!Number.isNaN(t)) { if (!c.expires || t < c.expires) c.expires = t; } }
    else if (k === "max-age") { const n = Number(v); if (Number.isFinite(n)) c.expires = Date.now() + n * 1000; }
    else if (k === "secure") c.secure = true;
    else if (k === "httponly") c.httpOnly = true;
    else if (k === "samesite") c.sameSite = v;
  }
  return c;
}

// Node gives set-cookie as an array through getSetCookie(); older output is one line.
function setCookieLines(r) {
  if (typeof r.headers.getSetCookie === "function") {
    const all = r.headers.getSetCookie();
    if (all && all.length) return all;
  }
  const one = r.headers.get("set-cookie");
  return one ? [one] : [];
}

function ensureSession(sid) {
  const now = Date.now();
  let s = sessions.get(sid);
  if (!s) { s = { seen: now, jars: new Map() }; sessions.set(sid, s); }
  s.seen = now;
  return s;
}

// Which session this request belongs to: header first, then ?sid=, then the cookie.
// Returns { sid, minted } — minted means it is new and should be handed back as a cookie.
function resolveSession(req, reqUrl, res) {
  const fromHeader = String(req.headers[SID_HEADER] || "").trim();
  const fromQuery = (reqUrl.searchParams.get(SID_PARAM) || "").trim();
  let fromCookie = "";
  for (const [k, v] of cookiePairs(req.headers.cookie)) if (k === SID_COOKIE) { fromCookie = v; break; }

  let sid = "";
  for (const cand of [fromHeader, fromQuery, fromCookie]) if (SID_RE.test(cand)) { sid = cand; break; }

  const minted = !sid;
  if (minted) sid = newSid();
  if (res) {
    res.setHeader(SID_HEADER, sid);
    if (sid !== fromCookie) {
      const attrs = ["Path=/", "HttpOnly", "Max-Age=" + Math.floor(SESSION_HOURS * 3600)];
      attrs.push(isHttps(req) ? "SameSite=None; Secure" : "SameSite=Lax");
      res.setHeader("Set-Cookie", SID_COOKIE + "=" + sid + "; " + attrs.join("; "));
    }
  }
  return { sid, session: ensureSession(sid) };
}

// The cookies a site has handed out that apply to this address, as [name, value] pairs.
function cookiesFor(session, url) {
  const host = url.hostname.toLowerCase();
  const pathname = url.pathname || "/";
  const now = Date.now();
  const out = [];
  for (const [domain, jar] of session.jars) {
    if (!(host === domain || host.endsWith("." + domain))) continue;
    for (const [key, c] of jar) {
      if (c.expires && c.expires <= now) { jar.delete(key); continue; }
      if (c.path && c.path !== "/" && !pathname.startsWith(c.path)) continue;
      if (c.secure && url.protocol !== "https:") continue;
      out.push([c.name, c.value]);
    }
  }
  return out;
}

// Remember every cookie a site just set. Cookies claiming another site's domain are
// ignored, so one site cannot plant cookies for another.
function storeCookies(session, url, lines) {
  const host = url.hostname.toLowerCase();
  for (const line of lines) {
    const c = parseSetCookie(line);
    if (!c) continue;
    const domain = c.domain || host;
    if (!(host === domain || host.endsWith("." + domain))) continue;
    let jar = session.jars.get(domain);
    if (!jar) { jar = new Map(); session.jars.set(domain, jar); }
    const key = (c.path || "/") + "|" + c.name;
    if (c.expires && c.expires <= Date.now()) { jar.delete(key); continue; }
    if (jar.size >= MAX_COOKIES_PER_SITE && !jar.has(key)) continue;
    jar.set(key, { name: c.name, value: c.value, path: c.path || "/", expires: c.expires || 0, secure: c.secure });
  }
}

function forgetSession(sid) {
  sessions.delete(sid);
}

setInterval(() => {
  const cutoff = Date.now() - SESSION_HOURS * 3600 * 1000;
  for (const [sid, s] of sessions) if (s.seen < cutoff) sessions.delete(sid);
}, 10 * 60 * 1000).unref();

// ---- Follow redirects by hand so every hop is checked, and report where we ended up ----
// onHop runs for every response, which is how cookies set by an early hop of a sign-in
// redirect chain are kept instead of being lost.
async function fetchFollow(url, init, cookieFn, onHop) {
  let cur = new URL(url);
  for (let i = 0; i <= MAX_REDIRECTS; i++) {
    await assertPublic(cur);
    const headers = { ...(init.headers || {}) };
    const jarCookies = cookieFn ? cookieFn(cur) : [];
    if (jarCookies.length) {
      const have = new Set(cookiePairs(headers.cookie).map(([k]) => k));
      const add = jarCookies.filter(([k]) => !have.has(k)).map(([k, v]) => k + "=" + v);
      if (add.length) headers.cookie = headers.cookie ? headers.cookie + "; " + add.join("; ") : add.join("; ");
    }
    const r = await fetch(cur, { ...init, headers, redirect: "manual", signal: AbortSignal.timeout(TIMEOUT_MS) });
    if (onHop) onHop(cur, r);
    const loc = r.headers.get("location");
    if (r.status >= 300 && r.status < 400 && loc) {
      cur = new URL(loc, cur);
      if ([301, 302, 303].includes(r.status) && init.method !== "GET" && init.method !== "HEAD") {
        init = { ...init, method: "GET", body: undefined };
      }
      continue;
    }
    return { res: r, finalUrl: cur.href };
  }
  throw new Error("Too many redirects");
}

// ---- Module mode: ES modules and the location references inside them ----
const LOC_RE = /(?:(?<![\w$.])|\b(?:window|document|top|self|parent)\.)location\.(href|origin|protocol|host|hostname|port|pathname|search|hash|assign|replace|reload|toString)\b/g;
function rewriteModule(src, baseUrl, proxyOrigin, sid) {
  const tail = sid ? "&sid=" + encodeURIComponent(sid) : "";
  const mod = (u) => proxyOrigin + "/proxy?mode=module&url=" + encodeURIComponent(u) + tail;
  src = src.replace(/(\bfrom\s*|\bimport\s*\(?\s*)(["'])([^"'\n]+)\2/g, (m, pre, q, spec) => {
    if (!/^(\.{0,2}\/|https?:\/\/)/.test(spec)) return m;      // bare names are left alone
    try { const u = new URL(spec, baseUrl); return /^https?:$/.test(u.protocol) ? pre + q + mod(u.href) + q : m; } catch (e) { return m; }
  });
  return src.replace(LOC_RE, "window.__nbLoc.$1")
    .replace(/\b(?:window|document|self|top|parent)\.location\s*=(?!=)/g, "window.__nbLoc.href=")
    .replace(/\b(?:window|document|self|top|parent)\.location\b/g, "window.__nbLoc")
    .replace(/\bdocument\.URL\b/g, "window.__nbLoc.href");
}

// ---- Browse mode: sends the page's fetch/XHR back through the proxy ----
// requests keep their body (so sign-in and other POSTs still go through) and the quick
// round trips a sign-in page makes are left alone.
function shim(proxyOrigin, baseUrl, sid) {
  const code = `(function(){var P=${JSON.stringify(proxyOrigin)},B=${JSON.stringify(baseUrl)},S=${JSON.stringify(sid || "")};
function w(u){try{var a=new URL(u,B);if(!/^https?:$/.test(a.protocol)||a.href.indexOf(P+"/")===0)return u;
return P+"/proxy?url="+encodeURIComponent(a.href)+(S?"&sid="+encodeURIComponent(S):"");}catch(e){return u}}
var f=window.fetch;window.fetch=function(i,o){
if(typeof i==="string"||i instanceof URL)return f.call(this,w(String(i)),o);
if(i&&i.url)return f.call(this,new Request(w(i.url),i),o);return f.apply(this,arguments)};
var x=XMLHttpRequest.prototype.open;XMLHttpRequest.prototype.open=function(m,u){arguments[1]=w(String(u));return x.apply(this,arguments)};
})();`;
  return "<script>" + code.replace(/<\//g, "<\\/") + "</script>";
}

function cors(req, res) {
  const origin = req.headers.origin;
  if (ALLOWED.includes("*")) {
    // Reflect the caller instead of "*" so credentialed (signed-in) requests are allowed.
    if (origin) { res.setHeader("Access-Control-Allow-Origin", origin); res.setHeader("Vary", "Origin"); }
    else res.setHeader("Access-Control-Allow-Origin", "*");
    res.setHeader("Access-Control-Allow-Credentials", "true");
  } else if (origin && ALLOWED.includes(origin)) {
    res.setHeader("Access-Control-Allow-Origin", origin);
    res.setHeader("Access-Control-Allow-Credentials", "true");
    res.setHeader("Vary", "Origin");
  }
  res.setHeader("Access-Control-Allow-Methods", "GET,POST,PUT,PATCH,DELETE,HEAD,OPTIONS");
  res.setHeader("Access-Control-Allow-Headers", "*, x-nb-session");
  res.setHeader("Access-Control-Expose-Headers", "x-final-url, x-nb-session");
}

function fail(res, status, message) {
  res.writeHead(status, { "Content-Type": "application/json; charset=utf-8", "Cache-Control": "no-store" });
  res.end(JSON.stringify({ error: message }));
}

async function handleProxy(req, res, reqUrl) {
  cors(req, res);
  if (req.method === "OPTIONS") { res.writeHead(204); return res.end(); }
  if (limited(req)) return fail(res, 429, "Too many requests. Slow down and try again in a minute.");
  const target = reqUrl.searchParams.get("url");
  if (!target) return fail(res, 400, "Missing ?url=");
  try { new URL(target); } catch (e) { return fail(res, 400, "That is not a valid address"); }
  const mode = reqUrl.searchParams.get("mode");
  const browse = mode === "browse";

  // Bound simultaneous upstream work so bursts cannot exhaust sockets or memory.
  // Excess requests fail fast instead of building an unbounded queue.
  const visitor = clientKey(req);
  const visitorActive = activeByClient.get(visitor) || 0;
  if (activeRequests >= MAX_CONCURRENT || visitorActive >= MAX_PER_CLIENT) {
    res.setHeader("Retry-After", "2");
    return fail(res, 503, "The proxy is busy. Please retry in a moment.");
  }
  activeRequests++;
  activeByClient.set(visitor, visitorActive + 1);

  try {
    // Which saved logins this request belongs to (and, if it is new, remember the id).
    const { sid, session } = resolveSession(req, reqUrl, res);

    // Cookies the page itself set (JS document.cookie) still ride along; the proxy's own
    // session cookie never goes upstream.
    const browserCookies = cookiePairs(req.headers.cookie)
      .filter(([k]) => k !== SID_COOKIE && k !== SID_PARAM);

    const headers = { "user-agent": DEFAULT_UA };
    for (const h of FORWARD_REQUEST_HEADERS) {
      if (req.headers[h]) headers[h] = req.headers[h];
    }
    // A sign-in POST that says it is a form must be copied as-is; content-length is
    // recalculated from the body we actually send.
    delete headers["content-length"];

    let body;
    if (!["GET", "HEAD"].includes(req.method)) {
      const chunks = []; let size = 0;
      for await (const c of req) { size += c.length; if (size > REQUEST_MAX_BYTES) return fail(res, 413, "Request too large"); chunks.push(c); }
      body = Buffer.concat(chunks);
    }

    // Every redirect hop carries the cookies the site handed out so far, and every hop's
    // Set-Cookie is kept. That is what makes a login flow (site -> auth site -> back)
    // work instead of dropping the visitor at a sign-in page again.
    const { res: r, finalUrl } = await fetchFollow(
      target,
      { method: req.method, headers, body },
      (u) => {
        const jar = cookiesFor(session, u);
        const names = new Set(jar.map(([k]) => k));
        return jar.concat(browserCookies.filter(([k]) => !names.has(k)));
      },
      (u, hr) => storeCookies(session, u, setCookieLines(hr)),
    );

    const type = r.headers.get("content-type") || "";
    // Only these two cases need the full text in memory, to rewrite it; everything else
    // (images, video, fonts, plain scripts, stylesheets, JSON, ...) is streamed straight
    // through below without ever being buffered, which is what lets large files work.
    const needsText = mode === "module" || (browse && type.includes("text/html"));
    const cap = needsText ? MAX_TEXT_BYTES : MAX_BYTES;

    const declared = Number(r.headers.get("content-length"));
    if (declared > cap) return fail(res, 413, "That file is too large for the proxy");

    for (const [k, v] of r.headers) if (!STRIP.has(k.toLowerCase())) res.setHeader(k, v);
    res.setHeader("x-final-url", finalUrl);
    res.setHeader("Cache-Control", "no-store");
    res.statusCode = r.status;
    if (req.method === "HEAD") return res.end();

    const proto = req.headers["x-forwarded-proto"] || (isHttps(req) ? "https" : "http");
    const origin = PUBLIC_URL || `${proto}://${req.headers.host}`;

    if (needsText) {
      // Content-Length isn't always sent (chunked responses), so also count bytes as they
      // arrive and bail out early rather than buffering an unbounded amount of text.
      const chunks = []; let total = 0;
      for await (const chunk of r.body) {
        total += chunk.length;
        if (total > cap) return fail(res, 413, "That file is too large for the proxy");
        chunks.push(chunk);
      }
      const text = Buffer.concat(chunks).toString("utf8");
      if (mode === "module") {
        res.setHeader("Content-Type", "text/javascript; charset=utf-8");
        return res.end(rewriteModule(text, finalUrl, origin, sid));
      }
      let html = text;
      const tag = shim(origin, finalUrl, sid);
      html = /<head[^>]*>/i.test(html) ? html.replace(/<head[^>]*>/i, (m) => m + tag) : tag + html;
      res.setHeader("Content-Type", "text/html; charset=utf-8");
      return res.end(html);
    }

    // Passthrough: stream the body straight to the visitor as it arrives, with a running
    // byte count that cuts the connection if a response with no declared size turns out
    // to be larger than the cap, so one huge, unmeasured download can't run away.
    let sent = 0;
    try {
      for await (const chunk of r.body) {
        sent += chunk.length;
        if (sent > cap) { res.destroy(); return; }
        if (!res.write(chunk)) await new Promise((resolve) => res.once("drain", resolve));
      }
      res.end();
    } catch (e) { try { res.destroy(); } catch (e2) {} }
  } catch (e) {
    const timedOut = e && (e.name === "TimeoutError" || e.name === "AbortError");
    if (!res.headersSent) fail(res, timedOut ? 504 : 502, timedOut ? "The site took too long to answer" : "Proxy error: " + e.message);
    else { try { res.destroy(); } catch (e2) {} }
  } finally {
    activeRequests--;
    const remaining = (activeByClient.get(visitor) || 1) - 1;
    if (remaining > 0) activeByClient.set(visitor, remaining);
    else activeByClient.delete(visitor);
  }
}

// ---- /session: what is signed in, and a way to sign out of everything ----
function handleSession(req, res, reqUrl) {
  const sid = resolveSession(req, reqUrl, res).sid;
  const session = sessions.get(sid);
  if (req.method === "DELETE") {
    forgetSession(sid);
    res.setHeader("Set-Cookie", SID_COOKIE + "=; Path=/; HttpOnly; Max-Age=0");
    res.writeHead(200, { "Content-Type": "application/json; charset=utf-8", "Cache-Control": "no-store" });
    return res.end(JSON.stringify({ ok: true, signedIn: [] }));
  }
  const sites = [];
  if (session) {
    for (const [domain, jar] of session.jars) {
      let live = 0;
      const now = Date.now();
      for (const c of jar.values()) if (!c.expires || c.expires > now) live++;
      if (live) sites.push({ site: domain, cookies: live });
    }
  }
  res.writeHead(200, { "Content-Type": "application/json; charset=utf-8", "Cache-Control": "no-store" });
  res.end(JSON.stringify({ ok: true, sid, signedIn: sites.sort((a, b) => a.site.localeCompare(b.site)) }));
}

const FILES = {
  "/": ["index.html", "text/html; charset=utf-8"],
  "/index.html": ["index.html", "text/html; charset=utf-8"],
  "/favicon.ico": ["favicon.ico", "image/x-icon"],
};

const server = http.createServer((req, res) => {
  let u;
  try { u = new URL(req.url, "http://localhost"); }
  catch (e) { return fail(res, 400, "Invalid request URL"); }
  if (u.pathname === "/proxy") return handleProxy(req, res, u);
  if (u.pathname === "/session") return handleSession(req, res, u);
  if (u.pathname === "/health") { res.writeHead(200, { "Content-Type": "text/plain" }); return res.end("ok"); }
  const f = FILES[u.pathname];
  if (f) {
    const file = path.join(__dirname, f[0]);
    if (!fs.existsSync(file)) { res.writeHead(404); return res.end("Not found"); }
    res.writeHead(200, { "Content-Type": f[1] });
    return fs.createReadStream(file).pipe(res);
  }
  res.writeHead(404); res.end("Not found");
});

// Bound slow headers and incoming requests without interfering with streamed responses.
server.headersTimeout = 15_000;
server.requestTimeout = 120_000;
server.keepAliveTimeout = 5_000;
server.maxHeadersCount = 100;
server.maxConnections = Math.max(MAX_CONCURRENT * 2, 200);

server.listen(PORT, () => {
  console.log(`Assignment Shortcuts proxy running at http://localhost:${PORT}`);
  console.log(`Concurrency limits: ${MAX_CONCURRENT} total, ${MAX_PER_CLIENT} per visitor`);
  console.log(`Logins are kept for ${SESSION_HOURS}h after a visitor's last request`);
});
