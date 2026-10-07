#!/usr/bin/env python3
"""Aggiorna in dati/ i numeri delle AUTOVETTURE usati dalla pagina «Trasporti – Strade».

Lo usa l'aggiornamento automatico su GitHub (.github/workflows/aggiorna-dati.yml, ogni giorno), ma si può lanciare
anche a mano:  python3 aggiorna_dati.py [--forza] [--accetta]        Solo libreria standard di Python (niente da installare;
per i file .rar serve un programma di sistema: bsdtar, 7z, unrar o unar: il workflow installa bsdtar).

COSA FA, in due parti indipendenti (se una ha un problema l'altra si aggiorna lo stesso):
  1. ACI (Automobile Club d'Italia). Legge la pagina «Open data» dell'ACI, trova da sola i file «Autoritratto» (uno per anno, in .zip o
     .rar: l'indirizzo contiene mese e anno di caricamento e cambia, per questo non è scritto nel programma), scarica l'ultimo
     (12 MB) quando esce una nuova edizione o quando il file viene ricaricato, ne apre i due fogli di calcolo che servono
     (Parco_veicolare_AAAA.ods e Circolante_Copert_AAAA.ods), li controlla e salva:
       - dati/aci_autovetture.csv        autovetture al 31 dicembre: 12 province lombarde, Lombardia (= somma delle 12) e Italia (= somma delle province);
       - dati/aci_varese_dettaglio.csv   Varese: autovetture per alimentazione e classe Euro (foglio Copert) e per cilindrata.
     Le edizioni già salvate non vengono toccate da quelle nuove. Controlli: fogli, intestazioni e righe attese; Lombardia e Italia = totali
     del file; ogni riga somma delle colonne = totale; Varese uguale nei due file; variazione sull'anno prima (oltre ±3% avviso, oltre ±8%
     blocco); stesso anno ricaricato con numeri diversi (oltre lo 0,5% blocco).
  2. ISTAT. Scarica la popolazione residente al 1° gennaio di Varese, Lombardia e Italia (serve per «autovetture ogni 100 abitanti»)
     e la salva in dati/istat_popolazione.csv. Riscarica solo se ISTAT dichiara un aggiornamento nuovo (LAST_UPDATE) o dopo 28 giorni.
Se qualcosa non va, i file della parte interessata NON vengono toccati e il problema viene scritto nel file di esito
(--esito): segnala_problemi.py apre una segnalazione (e-mail). Se non ci sono novità non è un problema.
  --forza     scarica e ricontrolla tutto anche se non ci sono novità
  --accetta   salva anche se un controllo di plausibilità segnala un'anomalia (da usare solo dopo aver verificato a mano)
Con la variabile d'ambiente PROVA_ERRORE=true si simula un problema (per provare l'e-mail).
"""
import argparse
import csv
import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
import zipfile
from datetime import datetime, timezone

CARTELLA = os.path.join(os.path.dirname(os.path.abspath(__file__)), "dati")
PAGINA_ACI = "https://aci.gov.it/attivita-e-progetti/studi-e-ricerche/open-data/"
SDMXWS = "https://esploradati.istat.it/SDMXWS/rest/"
FLUSSO_POP = "IT1,22_289_DF_DCIS_POPRES1_1,1.0"
FLUSSO_POP_RIC = "IT1,164_164_DF_DCIS_RICPOPRES2011_1,1.0"
ANNO_ISTAT_INIZIO = 2002
VARESE, REGIONE, ITALIA = "ITC41", "ITC4", "IT"
NOMI_LOMBARDI = ["Varese", "Como", "Sondrio", "Milano", "Bergamo", "Brescia", "Pavia", "Cremona", "Mantova", "Lecco", "Lodi",
                 "Monza e della Brianza"]
TERRITORI = NOMI_LOMBARDI + ["Lombardia", "Italia"]                    # ordine dei file CSV
# nome della provincia nei fogli ACI (senza spazi né segni) -> nome usato nelle tabelle
PROVINCE_ACI = {"VARESE": "Varese", "COMO": "Como", "SONDRIO": "Sondrio", "MILANO": "Milano", "BERGAMO": "Bergamo", "BRESCIA": "Brescia",
                "PAVIA": "Pavia", "CREMONA": "Cremona", "MANTOVA": "Mantova", "LECCO": "Lecco", "LODI": "Lodi",
                "MONZABRIANZA": "Monza e della Brianza", "MONZAEBRIANZA": "Monza e della Brianza", "MONZAEDELLABRIANZA": "Monza e della Brianza"}
CSV_AUT = ["anno", "territorio", "autovetture", "fonte"]
CSV_DET = ["anno", "tavola", "riga", "colonna", "valore"]
CSV_POP = ["anno", "territorio", "popolazione", "stato"]
CILINDRATE = ["FINO A 800", "801 - 1200", "1201 - 1600", "1601 - 1800", "1801 - 2000", "2001 - 2500", "2501 - 3000", "OLTRE 3000", "NON DEFINITO"]
COLONNE_FISSE_COPERT = ["NON CONTEMPLATO", "NON DEFINITO", "TOTALE"]
SOGLIA_AVVISO = 0.03      # variazione annua oltre ±3%: avviso
SOGLIA_BLOCCO = 0.08      # oltre ±8%: blocco
SCARTO_AVVISO = 0.03      # crescita di Varese diversa da quella dell'Italia di oltre 3 punti: avviso
SCARTO_BLOCCO = 0.06      # oltre 6 punti: blocco
SOGLIA_RICARICA = 0.005   # stesso anno ricaricato: cambiamenti oltre lo 0,5% su un territorio = blocco
PAUSA_ISTAT = 13          # ISTAT accetta circa 5 richieste al minuto per indirizzo
PAUSE_SITO = [30, 90, 180]
PAUSE_ISTAT_TENTATIVI = [60, 180, 300]
TIMEOUT = 300
GIORNI_MAX_ISTAT = 28
ANNO_MINIMO_ACI = 2019    # le edizioni dell'Autoritratto in open data partono dal 2019
USER_AGENT = "Mozilla/5.0 (report-trasporti; Camera di Commercio di Varese)"
STRUMENTI_RAR = [("bsdtar", ["-xf", "{a}", "-C", "{o}"]), ("7zz", ["x", "-y", "-o{o}", "{a}"]), ("7z", ["x", "-y", "-o{o}", "{a}"]),
                 ("unrar", ["x", "-y", "{a}", "{o}/"]), ("unar", ["-o", "{o}", "{a}"])]


class Problema(Exception):
    """tipo: "rete" (il sito non risponde), "risposta" (risponde ma non con quello che serve), "formato" (il file o la
    tavola sono cambiati), "anomalia" (numeri non plausibili o diversi da quelli già salvati), "prova" (simulato)."""
    def __init__(self, tipo, dettaglio):
        super().__init__(dettaglio)
        self.tipo = tipo


def ora():
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# ---------------------------------------------------------------------------------------------------- rete
def richiesta(url, accept, pause, nome_sito, metodo="GET"):
    """-> (contenuto, intestazioni). Riprova dopo le pause indicate."""
    errore = None
    for n in range(len(pause) + 1):
        try:
            req = urllib.request.Request(url, method=metodo, headers={"Accept": accept, "Accept-Language": "it, en;q=0.5", "User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=TIMEOUT) as r:
                return (b"" if metodo == "HEAD" else r.read()), {k.lower(): v for k, v in r.headers.items()}
        except Exception as e:  # rete, 429, 5xx, timeout
            errore = e
            print(f"  tentativo {n + 1} non riuscito: {e}", flush=True)
            if n < len(pause):
                time.sleep(pause[n])
    n = len(pause) + 1
    raise Problema("rete", f"il sito {nome_sito} non ha risposto ({n} {'tentativo' if n == 1 else 'tentativi'}): {errore}")


def scarica(url, accept, pause, nome_sito):
    return richiesta(url, accept, pause, nome_sito)[0]


# ---------------------------------------------------------------------------------------------------- ACI: pagina, archivi, fogli ODS
def trova_edizioni(pagina_html):
    """Pagina «Open data» dell'ACI -> [{anno, url, nome}] delle edizioni dell'Autoritratto, dalla più vecchia alla più recente."""
    trovate = {}
    for m in re.finditer(r"<a\b[^>]*?href=\"([^\"]+)\"", pagina_html, re.I):
        href = m.group(1).replace("&amp;", "&")
        nome = urllib.parse.unquote(href.rsplit("/", 1)[-1])
        if re.search(r"autoritratto", nome, re.I) and re.search(r"\.(zip|rar|7z)$", nome, re.I):
            a = re.search(r"(20\d\d)", nome)
            if a:
                url = urllib.parse.urljoin(PAGINA_ACI, re.sub(r"(?<!:)//+", "/", href))
                trovate[int(a.group(1))] = {"anno": int(a.group(1)), "url": url, "nome": nome}
    if not trovate:
        raise Problema("formato", "nella pagina «Open data» dell'ACI non trovo più i file «Autoritratto» (la pagina è stata cambiata o i file sono stati tolti)")
    return [trovate[a] for a in sorted(trovate)]


def trova_strumento_rar():
    for nome, argomenti in STRUMENTI_RAR:
        percorso = shutil.which(nome)
        if percorso:
            return percorso, argomenti
    return None, None


def estrai_archivio(dati, cartella, livello=0):
    """Scrive in `cartella` i file .ods dell'archivio (zip, anche annidati, oppure rar con un programma di sistema)."""
    if livello > 3:
        return
    os.makedirs(cartella, exist_ok=True)
    if dati[:2] == b"PK":
        try:
            z = zipfile.ZipFile(io.BytesIO(dati))
            membri = [i for i in z.infolist() if not i.is_dir()]
        except zipfile.BadZipFile as e:
            raise Problema("risposta", f"il file scaricato dall'ACI non è un archivio ZIP valido: {e}")
        for i in membri:
            base = os.path.basename(i.filename.replace("\\", "/"))
            if re.search(r"\.ods$", base, re.I):
                with open(os.path.join(cartella, f"{len(os.listdir(cartella))}_{base}"), "wb") as f:
                    f.write(z.read(i))
            elif re.search(r"\.zip$", base, re.I):
                estrai_archivio(z.read(i), cartella, livello + 1)
    elif dati[:4] == b"Rar!":
        strumento, argomenti = trova_strumento_rar()
        if not strumento:
            raise Problema("formato", "l'ACI ha pubblicato il file in formato .rar e sul computer non c'è nessun programma per aprirlo "
                                      "(servono bsdtar, 7z, unrar o unar: nel workflow GitHub si installa con «sudo apt-get install libarchive-tools»)")
        with tempfile.TemporaryDirectory() as tmp:
            arc = os.path.join(tmp, "archivio.rar")
            usc = os.path.join(tmp, "estratto")
            os.makedirs(usc)
            with open(arc, "wb") as f:
                f.write(dati)
            comando = [strumento] + [x.format(a=arc, o=usc) for x in argomenti]
            r = subprocess.run(comando, capture_output=True, text=True, timeout=600)
            if r.returncode != 0:
                raise Problema("risposta", f"non riesco ad aprire il file .rar dell'ACI ({os.path.basename(strumento)}: {(r.stderr or r.stdout).strip()[:300]})")
            for radice, _, nomi in os.walk(usc):
                for n in sorted(nomi):
                    p = os.path.join(radice, n)
                    if re.search(r"\.ods$", n, re.I):
                        shutil.copy(p, os.path.join(cartella, f"{len(os.listdir(cartella))}_{n}"))
                    elif re.search(r"\.zip$", n, re.I):
                        with open(p, "rb") as f:
                            estrai_archivio(f.read(), cartella, livello + 1)
    else:
        raise Problema("risposta", "il file scaricato dall'ACI non è né uno ZIP né un RAR (forse una pagina di errore)")


def trova_ods(cartella, anno):
    """-> (percorso di Parco_veicolare, percorso di Circolante_Copert)."""
    parco = copert = None
    visti = []
    for n in sorted(os.listdir(cartella)):
        nome = re.sub(r"^\d+_", "", n).lower().replace(" ", "_")
        visti.append(nome)
        if re.fullmatch(rf"parco_veicolare_?{anno}\.ods", nome):
            parco = os.path.join(cartella, n)
        elif re.fullmatch(rf"circolante_copert_?{anno}\.ods", nome):
            copert = os.path.join(cartella, n)
    if not parco or not copert:
        raise Problema("formato", f"nell'archivio ACI del {anno} non trovo i file Parco_veicolare_{anno}.ods e Circolante_Copert_{anno}.ods "
                                  f"(trovati: {', '.join(visti) or 'nessun .ods'})")
    return parco, copert


T_NS = "{urn:oasis:names:tc:opendocument:xmlns:table:1.0}"
O_NS = "{urn:oasis:names:tc:opendocument:xmlns:office:1.0}"
X_NS = "{urn:oasis:names:tc:opendocument:xmlns:text:1.0}"


def nome_foglio(nome):
    """'27_AV_Provincia_cilindrata' -> 'av_provincia_cilindrata' (senza il numero iniziale)."""
    return re.sub(r"[\s_]+", "_", re.sub(r"^\d+[_ ]*", "", nome.strip())).lower()      # le edizioni vecchie hanno spazi invece di «_»


def leggi_ods(percorso, fogli):
    """Legge solo i fogli voluti. fogli = {chiave: nome normalizzato del foglio}. -> {chiave: righe}; ogni riga è una lista di valori
    (testo, numero o None); le righe vuote sono liste vuote. Lettura a flusso (il file Copert è 90 MB di XML)."""
    out, corrente, righe, nomi = {}, None, None, []
    try:
        z = zipfile.ZipFile(percorso)
        flusso = z.open("content.xml")
    except Exception as e:
        raise Problema("formato", f"il foglio di calcolo {os.path.basename(percorso)} non è un file ODS valido: {e}")
    with flusso:
        try:
            for ev, el in ET.iterparse(flusso, events=("start", "end")):
                if ev == "start":
                    if el.tag == T_NS + "table":
                        corrente = el.get(T_NS + "name") or ""
                        nomi.append(corrente)
                        voluta = [k for k, v in fogli.items() if nome_foglio(corrente) == v]
                        righe = [] if voluta else None
                        chiave = voluta[0] if voluta else None
                    continue
                if el.tag == T_NS + "table-row":
                    if righe is not None:
                        riga, vuota = [], True
                        for c in el:
                            if c.tag not in (T_NS + "table-cell", T_NS + "covered-table-cell"):
                                continue
                            n = int(c.get(T_NS + "number-columns-repeated", "1"))
                            tipo = c.get(O_NS + "value-type")
                            if tipo in ("float", "percentage", "currency"):
                                v = float(c.get(O_NS + "value"))
                            elif tipo:
                                v = "\n".join("".join(p.itertext()) for p in c.findall(X_NS + "p"))
                            else:
                                v = None
                            if v is not None:
                                vuota = False
                            if v is not None:
                                riga.extend([v] * min(n, 64))
                            elif n <= 64:
                                riga.extend([None] * n)
                        while riga and riga[-1] is None:
                            riga.pop()
                        rip = int(el.get(T_NS + "number-rows-repeated", "1"))
                        if vuota:
                            righe.append([])
                        else:
                            righe.extend([riga] * min(rip, 2000))
                    el.clear()
                elif el.tag == T_NS + "table":
                    if righe is not None:
                        out[chiave] = righe
                    righe = None
                    el.clear()
        except ET.ParseError as e:
            raise Problema("formato", f"il foglio di calcolo {os.path.basename(percorso)} non si legge (XML non valido): {e}")
    mancano = [k for k in fogli if k not in out]
    if mancano:
        raise Problema("formato", f"in {os.path.basename(percorso)} non trovo i fogli {', '.join(fogli[k] for k in mancano)} "
                                  f"(fogli presenti: {', '.join(nomi[:40])})")
    return out


def maiusc(v):
    return re.sub(r"\s+", " ", str(v)).strip().upper() if isinstance(v, str) else ""


def senza_segni(v):
    return re.sub(r"[^A-Z]", "", maiusc(v))


def intestazione(c):
    """Intestazione di colonna in maiuscolo; «Totale complessivo» (usato da alcune edizioni) = «TOTALE»."""
    t = maiusc(c)
    return "TOTALE" if t.startswith("TOTALE") else t


def trova_intestazione(righe, richieste, nome):
    for i, r in enumerate(righe[:15]):
        celle = {intestazione(c) for c in r if isinstance(c, str)}
        if all(x in celle for x in richieste):
            return i, [intestazione(c) for c in r]
    raise Problema("formato", f"nel foglio «{nome}» non trovo la riga di intestazione con {', '.join(richieste)} (il file ACI è cambiato)")


def titolo_anno(righe, anno, nome):
    for r in righe[:3]:
        for c in r:
            if isinstance(c, str):
                a = re.search(r"anno (\d{4})", c, re.I)
                if a:
                    if int(a.group(1)) != anno:
                        raise Problema("formato", f"il foglio «{nome}» dice «Anno {a.group(1)}» ma l'edizione è la {anno}")
                    return
    raise Problema("formato", f"nel foglio «{nome}» manca il titolo «… Anno {anno}»")


def num(v):
    if v is None:
        return 0.0
    if isinstance(v, str):
        raise Problema("formato", f"trovo il testo «{v}» dove dovrebbe esserci un numero (il file ACI è cambiato)")
    return float(v)


def parse_autovetture(righe, anno):
    """Foglio «Provincia_categoria» -> ({(regione, provincia): autovetture}, {regione: totale}, totale nazionale)."""
    titolo_anno(righe, anno, "1_Provincia_categoria")
    h, testa = trova_intestazione(righe, ["REGIONE", "PROVINCIA", "AUTOVETTURE"], "1_Provincia_categoria")
    jr, jp, ja = testa.index("REGIONE"), testa.index("PROVINCIA"), testa.index("AUTOVETTURE")
    prov, tot_reg, nazionale, regione, riepilogo = {}, {}, None, None, False
    for r in righe[h + 1:]:
        g = lambda j: r[j] if j < len(r) else None
        reg, pr = g(jr), g(jp)
        if isinstance(reg, str) and maiusc(reg) == "RIEPILOGO":
            riepilogo = True
            continue
        if riepilogo:
            if isinstance(reg, str) and "TOTALE NAZIONALE" in maiusc(reg):
                nazionale = num(g(ja))
            continue
        if isinstance(reg, str) and reg.strip() and "TOTALE" not in maiusc(reg):
            regione = maiusc(reg)
        if not isinstance(pr, str) or not pr.strip():
            continue
        if maiusc(pr) == "TOTALE":
            tot_reg[regione] = num(g(ja))
        else:
            prov[(regione, maiusc(pr))] = num(g(ja))
    if not prov or nazionale is None:
        raise Problema("formato", "nel foglio «1_Provincia_categoria» mancano le province o il «Totale NAZIONALE» (il file ACI è cambiato)")
    return prov, tot_reg, nazionale


def parse_cilindrata(righe, anno):
    """Foglio «AV_Provincia_cilindrata» -> {nome provincia: {colonna: valore}} (tutte le province)."""
    titolo_anno(righe, anno, "AV_Provincia_cilindrata")
    h, testa = trova_intestazione(righe, ["PROVINCIA", "FINO A 800", "TOTALE"], "AV_Provincia_cilindrata")
    jp = testa.index("PROVINCIA")
    colonne = [(j, c) for j, c in enumerate(testa) if j > jp and c]
    ignote = [c for _, c in colonne if c not in CILINDRATE + ["TOTALE"]]
    if ignote:
        raise Problema("formato", f"nel foglio «AV_Provincia_cilindrata» ci sono fasce di cilindrata nuove o cambiate: {', '.join(ignote)}")
    mancano = [c for c in CILINDRATE + ["TOTALE"] if c not in [x for _, x in colonne]]
    if mancano:
        raise Problema("formato", f"nel foglio «AV_Provincia_cilindrata» mancano le fasce {', '.join(mancano)}")
    out = {}
    for r in righe[h + 1:]:
        pr = r[jp] if jp < len(r) else None
        if any(isinstance(x, str) for x in r[jp + 1:]):
            continue                                   # seconda intestazione o nota in fondo al foglio
        if isinstance(pr, str) and pr.strip() and maiusc(pr) != "TOTALE":
            out[senza_segni(pr)] = {c: num(r[j] if j < len(r) else None) for j, c in colonne}
    return out


def parse_copert(righe, anno):
    """Foglio «AV_per_Provincia» (Circolante Copert) -> {sigla provincia: {alimentazione: {colonna: valore}}}; 'TOTALE' = totale provincia."""
    titolo_anno(righe, anno, "3_AV_per_Provincia")
    h, testa = trova_intestazione(righe, ["PROVINCIA", "ALIMENTAZIONE", "FASCIA", "EURO 0"], "3_AV_per_Provincia")
    jp, jal, jf = testa.index("PROVINCIA"), testa.index("ALIMENTAZIONE"), testa.index("FASCIA")
    colonne = [(j, c) for j, c in enumerate(testa) if j > jf and c]
    ignote = [c for _, c in colonne if not (re.fullmatch(r"EURO [0-6][A-Z]?", c) or c in COLONNE_FISSE_COPERT)]
    if ignote:
        raise Problema("formato", f"nel foglio «3_AV_per_Provincia» ci sono classi Euro nuove o colonne cambiate: {', '.join(ignote)} "
                                  "(le tabelle prevedono Euro 0-6: serve decidere dove metterle)")
    if "TOTALE" not in [c for _, c in colonne]:
        raise Problema("formato", "nel foglio «3_AV_per_Provincia» manca la colonna «Totale»")
    out, prov, al = {}, None, None
    for r in righe[h + 1:]:
        g = lambda j: r[j] if j < len(r) else None
        if isinstance(g(jp), str) and g(jp).strip():
            prov = senza_segni(g(jp))
        if isinstance(g(jal), str) and g(jal).strip():
            al = maiusc(g(jal))
        if prov is None or al is None:
            continue
        fascia = maiusc(g(jf)) if isinstance(g(jf), str) else ""
        if al == "TOTALE" or fascia == "TOTALE":
            out.setdefault(prov, {})["TOTALE" if al == "TOTALE" else al] = {c: num(g(j)) for j, c in colonne}
    return out


def somma_aci(d, esclusi=("TOTALE",)):
    return sum(v for k, v in d.items() if k not in esclusi)


def elabora_edizione(anno, parco, copert):
    """Fogli ACI di un'edizione -> (righe aut [(territorio, valore)], righe dettaglio [(tavola, riga, colonna, valore)], descrizione dei controlli).
    Fa i controlli di coerenza interna (bloccanti)."""
    fp = leggi_ods(parco, {"cat": "provincia_categoria", "cil": "av_provincia_cilindrata"})
    prov, tot_reg, nazionale = parse_autovetture(fp["cat"], anno)
    cil = parse_cilindrata(fp["cil"], anno)
    cop = parse_copert(leggi_ods(copert, {"eu": "av_per_provincia"})["eu"], anno)
    lombarde = {}
    for (reg, p), v in prov.items():
        if reg == "LOMBARDIA":
            nome = PROVINCE_ACI.get(senza_segni(p))
            if nome is None:
                raise Problema("formato", f"provincia lombarda «{p}» non riconosciuta nel foglio ACI (nomi cambiati?)")
            lombarde[nome] = v
    mancano = [n for n in NOMI_LOMBARDI if n not in lombarde]
    if mancano:
        raise Problema("formato", f"nel foglio ACI mancano le province lombarde {', '.join(mancano)}")
    lombardia = sum(lombarde.values())
    if "LOMBARDIA" in tot_reg and abs(tot_reg["LOMBARDIA"] - lombardia) > 0.5:
        raise Problema("anomalia", f"la somma delle 12 province lombarde ({lombardia:.0f}) non coincide con il totale Lombardia del file ({tot_reg['LOMBARDIA']:.0f})")
    italia = sum(prov.values())
    if abs(italia - nazionale) > 0.5:
        raise Problema("anomalia", f"la somma delle province ({italia:.0f}) non coincide con il «Totale NAZIONALE» del file ({nazionale:.0f})")
    if not 300000 <= lombarde["Varese"] <= 900000 or not 25e6 <= italia <= 60e6:
        raise Problema("anomalia", f"numeri non plausibili: Varese {lombarde['Varese']:.0f}, Italia {italia:.0f}")
    # Varese nei fogli Copert e cilindrata: stessi totali del foglio principale
    if "VARESE" not in cop or "VARESE" not in cil:
        raise Problema("formato", "Varese non c'è nel foglio Copert o nel foglio delle cilindrate")
    cv, cc = cop["VARESE"], cil["VARESE"]
    if "TOTALE" not in cv:
        raise Problema("formato", "nel foglio Copert manca la riga «Totale» di Varese")
    if abs(cv["TOTALE"]["TOTALE"] - lombarde["Varese"]) > 0.5:
        raise Problema("anomalia", f"Varese: {cv['TOTALE']['TOTALE']:.0f} autovetture nel foglio Copert, {lombarde['Varese']:.0f} nel foglio principale")
    if abs(cc["TOTALE"] - lombarde["Varese"]) > 0.5:
        raise Problema("anomalia", f"Varese: {cc['TOTALE']:.0f} autovetture nel foglio delle cilindrate, {lombarde['Varese']:.0f} nel foglio principale")
    if abs(somma_aci(cc) - cc["TOTALE"]) > 0.5:
        raise Problema("anomalia", f"Varese, cilindrate: la somma delle fasce ({somma_aci(cc):.0f}) non coincide con il totale ({cc['TOTALE']:.0f})")
    for al, riga in cv.items():
        s = sum(v for k, v in riga.items() if k != "TOTALE")
        if abs(s - riga["TOTALE"]) > 0.5:
            raise Problema("anomalia", f"Varese, alimentazione {al}: la somma delle classi Euro ({s:.0f}) non coincide con il totale ({riga['TOTALE']:.0f})")
    for col in cv["TOTALE"]:
        s = sum(r[col] for k, r in cv.items() if k != "TOTALE")
        if abs(s - cv["TOTALE"][col]) > 0.5:
            raise Problema("anomalia", f"Varese, colonna {col}: la somma delle alimentazioni ({s:.0f}) non coincide con il totale ({cv['TOTALE'][col]:.0f})")
    aut = [(n, lombarde[n]) for n in NOMI_LOMBARDI] + [("Lombardia", lombardia), ("Italia", italia)]
    det = []
    for al in sorted(cv, key=lambda k: (k == "TOTALE", k)):
        for col, v in cv[al].items():
            if v:
                det.append(("copert", al, col, v))
    for col in CILINDRATE + ["TOTALE"]:
        det.append(("cilindrata", "VARESE", col, cc[col]))
    return aut, det


# ---------------------------------------------------------------------------------------------------- archivio CSV
def leggi_csv_file(percorso, campi):
    if not os.path.exists(percorso):
        return []
    with open(percorso, encoding="utf-8") as f:
        r = csv.DictReader(f)
        if r.fieldnames != campi:
            raise Problema("formato", f"il file {os.path.basename(percorso)} salvato ha colonne diverse da quelle attese ({r.fieldnames})")
        return list(r)


def scrivi_csv_file(percorso, campi, righe):
    buf = io.StringIO()
    w = csv.writer(buf, lineterminator="\n")
    w.writerow(campi)
    w.writerows(righe)
    nuovo = buf.getvalue()
    vecchio = open(percorso, encoding="utf-8").read() if os.path.exists(percorso) else None
    if vecchio == nuovo:
        return False
    with open(percorso + ".tmp", "w", encoding="utf-8", newline="") as f:
        f.write(nuovo)
    os.replace(percorso + ".tmp", percorso)
    return True


def formato_num(v):
    return str(int(v)) if float(v) == int(v) else repr(float(v))


def p_aut():
    return os.path.join(CARTELLA, "aci_autovetture.csv")


def p_det():
    return os.path.join(CARTELLA, "aci_varese_dettaglio.csv")


def p_pop():
    return os.path.join(CARTELLA, "istat_popolazione.csv")


def carica_aut():
    """{anno: {territorio: (valore, fonte)}}"""
    out = {}
    for r in leggi_csv_file(p_aut(), CSV_AUT):
        out.setdefault(int(r["anno"]), {})[r["territorio"]] = (float(r["autovetture"]), r["fonte"])
    return out


def carica_det():
    """{anno: [(tavola, riga, colonna, valore)]}"""
    out = {}
    for r in leggi_csv_file(p_det(), CSV_DET):
        out.setdefault(int(r["anno"]), []).append((r["tavola"], r["riga"], r["colonna"], float(r["valore"])))
    return out


def righe_aut(aut):
    ordine = {n: i for i, n in enumerate(TERRITORI)}
    return [[a, t, formato_num(v), f] for a in sorted(aut) for t, (v, f) in sorted(aut[a].items(), key=lambda x: ordine.get(x[0], 99))]


def righe_det(det):
    return [[a, t, r, c, formato_num(v)] for a in sorted(det) for t, r, c, v in det[a]]


def controlla_con_anno_prima(anno, nuovo, aut, avvisi, accetta):
    """Variazione sull'anno prima (archivio): Varese, Lombardia, Italia."""
    prima = aut.get(anno - 1)
    if not prima:
        avvisi.append(f"nell'archivio non ci sono le autovetture del {anno - 1}: nessun confronto con l'anno prima")
        return
    var = {}
    for n in ("Varese", "Lombardia", "Italia"):
        if n in prima and prima[n][0] and n in nuovo:
            var[n] = nuovo[n] / prima[n][0] - 1
    ita = var.get("Italia")
    fuori = [(n, g) for n, g in var.items() if abs(g) > SOGLIA_AVVISO]
    scarto = ita is not None and "Varese" in var and abs(var["Varese"] - ita) > SCARTO_AVVISO
    grave = any(abs(g) > SOGLIA_BLOCCO for _, g in fuori) or (scarto and abs(var["Varese"] - ita) > SCARTO_BLOCCO)
    testo = ", ".join(f"{n} {g * 100:+.2f}%" for n, g in var.items())
    if grave and not accetta:
        raise Problema("anomalia", f"variazione {anno}/{anno - 1} fuori dalla norma ({testo}): dati NON salvati. Verificare il file ACI e, "
                                   "se è giusto, rilanciare con «Accetta»")
    if fuori or scarto:
        avvisi.append(f"variazione {anno}/{anno - 1} insolita: {testo}")


def parte_aci(info, args, esiti, problemi, avvisi):
    nome = "aci"
    salvato = info.get(nome, {})
    print("ACI: leggo la pagina «Open data»…", flush=True)
    pagina = scarica(PAGINA_ACI, "text/html", PAUSE_SITO, "dell'ACI").decode("utf-8", "replace")
    edizioni = trova_edizioni(pagina)
    ultima = edizioni[-1]
    print(f"ACI: edizioni trovate {', '.join(str(e['anno']) for e in edizioni)}; ultima {ultima['anno']} → {ultima['url']}", flush=True)
    aut, det = carica_aut(), carica_det()
    # controllo leggero del file più recente: dimensione e data di caricamento (una richiesta HEAD)
    try:
        _, h = richiesta(ultima["url"], "*/*", PAUSE_SITO[:1], "dell'ACI", "HEAD")
        dimensione, modificato = int(h.get("content-length", "0") or 0), h.get("last-modified", "")
    except Exception:                      # se il sito non risponde alla richiesta leggera si scarica il file
        dimensione, modificato = 0, ""
    cambiato = (salvato.get("url") != ultima["url"] or salvato.get("dimensione") != dimensione or salvato.get("ultima_modifica") != modificato)
    da_fare = []
    for e in edizioni:
        if e["anno"] < max(ANNO_MINIMO_ACI, ultima["anno"] - 1):
            continue
        manca = e["anno"] not in det
        if manca or args.forza or (e is ultima and cambiato):
            da_fare.append(e)
    if not da_fare:
        salvato["controllato"] = ora()
        info[nome] = salvato
        esiti.append({"parte": nome, "novita": False, "anno": max(det) if det else None})
        print("ACI: nessuna novità (stesso file già salvato).", flush=True)
        return
    ultimo_salvato = max(det) if det else None
    if ultimo_salvato and ultima["anno"] < ultimo_salvato:
        raise Problema("anomalia", f"l'ultima edizione ACI in linea è del {ultima['anno']}, ma l'archivio ha già il {ultimo_salvato}: tenuto l'archivio")
    nuovi_aut = {a: dict(v) for a, v in aut.items()}
    nuovi_det = dict(det)
    sha, dim_file = None, None
    for e in sorted(da_fare, key=lambda x: x["anno"]):
        print(f"ACI: scarico l'edizione {e['anno']}…", flush=True)
        dati = scarica(e["url"], "*/*", PAUSE_SITO, "dell'ACI")
        if e is ultima:
            sha, dim_file = hashlib.sha256(dati).hexdigest(), len(dati)
        with tempfile.TemporaryDirectory() as tmp:
            estrai_archivio(dati, tmp)
            parco, copert = trova_ods(tmp, e["anno"])
            a, d = elabora_edizione(e["anno"], parco, copert)
        valori = dict(a)
        controlla_con_anno_prima(e["anno"], valori, nuovi_aut, avvisi, args.accetta)
        vecchio = nuovi_aut.get(e["anno"])
        if vecchio:
            diff = {t: (vecchio[t][0], valori[t]) for t in valori if t in vecchio and vecchio[t][0] != valori[t]}
            grandi = [t for t, (o, n) in diff.items() if o and abs(n / o - 1) > SOGLIA_RICARICA]
            if grandi and not args.accetta:
                raise Problema("anomalia", f"l'edizione ACI del {e['anno']} ha numeri diversi da quelli già salvati ({', '.join(f'{t}: {diff[t][0]:.0f} → {diff[t][1]:.0f}' for t in grandi[:4])}): "
                                           "dati NON sostituiti. Verificare e, se giusto, rilanciare con «Accetta»")
            if diff:
                esempi = ", ".join(f"{t}: {o:.0f} → {n:.0f}" for t, (o, n) in list(diff.items())[:3])
                avvisi.append(f"l'edizione ACI del {e['anno']} ha numeri diversi da quelli già salvati ({len(diff)} territori, ad esempio {esempi}): sostituiti"
                              + (" (erano quelli dell'archivio iniziale, scritto a mano)" if all(vecchio[t][1] != "aci" for t in diff) else ""))
        nuovi_aut[e["anno"]] = {t: (v, "aci") for t, v in valori.items()}
        nuovi_det[e["anno"]] = d
        print(f"ACI: {e['anno']}: Varese {valori['Varese']:.0f}, Lombardia {valori['Lombardia']:.0f}, Italia {valori['Italia']:.0f}", flush=True)
    m1 = scrivi_csv_file(p_aut(), CSV_AUT, righe_aut(nuovi_aut))
    m2 = scrivi_csv_file(p_det(), CSV_DET, righe_det(nuovi_det))
    modificato_dati = m1 or m2
    info[nome] = {"anno": ultima["anno"], "url": ultima["url"], "nome_file": ultima["nome"], "dimensione": dimensione or dim_file,
                  "ultima_modifica": modificato, "sha256": sha or salvato.get("sha256"), "scaricato": ora(), "controllato": ora(),
                  "anni_dettaglio": sorted(nuovi_det), "dati_modificati": ora() if modificato_dati else salvato.get("dati_modificati", ora())}
    esiti.append({"parte": nome, "novita": modificato_dati, "anno": max(nuovi_det)})
    print(f"ACI: {'SALVATO' if modificato_dati else 'invariato'} (anni con dettaglio: {', '.join(map(str, sorted(nuovi_det)))})", flush=True)


# ---------------------------------------------------------------------------------------------------- ISTAT
def url_dati(flusso, chiave, inizio):
    return f"{SDMXWS}data/{flusso}/{chiave}?startPeriod={inizio}&format=csvfile"


def ultimo_aggiornamento(flusso):
    """Data di ultimo aggiornamento dichiarata da ISTAT per il dataflow (facoltativa: se non c'è, None)."""
    try:
        xml = scarica(f"{SDMXWS}dataflow/{flusso.replace(',', '/')}?references=none", "application/xml", [], "ISTAT").decode("utf-8", "replace")
        i = xml.find('id="LAST_UPDATE"')
        a = xml.find("<common:AnnotationTitle>", i)
        b = xml.find("</common:AnnotationTitle>", a)
        return xml[a + 24:b] if i > 0 and a > 0 and b > a else None
    except Exception:
        return None


def leggi_csv_istat(dati, richieste, nome):
    testo = dati.decode("utf-8-sig", "replace")
    prima = testo.split("\n", 1)[0]
    if not all(c in prima for c in richieste):
        raise Problema("risposta", f"ISTAT ha risposto, ma non con il CSV dei dati «{nome}» (inizio: «{testo[:120].strip()[:120]}»)")
    return list(csv.DictReader(io.StringIO(testo)))


def serie_popolazione(righe_attuali, righe_ric):
    """-> {territorio: {anno: (popolazione, stato)}}. La serie attuale ha la precedenza sulla ricostruzione."""
    codici = {VARESE: "Varese", REGIONE: "Lombardia", ITALIA: "Italia"}
    pop = {"Varese": {}, "Lombardia": {}, "Italia": {}}
    for righe in (righe_attuali, righe_ric):
        for r in righe:
            if r["REF_AREA"] in codici and r["OBS_VALUE"] not in ("", None):
                try:
                    anno, val = int(r["TIME_PERIOD"]), float(r["OBS_VALUE"])
                except ValueError:
                    raise Problema("formato", f"valore o periodo non numerico nel CSV ISTAT (periodo «{r['TIME_PERIOD']}», valore «{r['OBS_VALUE']}»)")
                pop[codici[r["REF_AREA"]]].setdefault(anno, (val, (r.get("OBS_STATUS") or "").strip()))
    return pop


def carica_pop():
    pop = {"Varese": {}, "Lombardia": {}, "Italia": {}}
    for r in leggi_csv_file(p_pop(), CSV_POP):
        pop[r["territorio"]][int(r["anno"])] = (float(r["popolazione"]), r["stato"])
    return pop


def righe_pop(pop):
    return [[y, t, formato_num(pop[t][y][0]), pop[t][y][1]] for t in ("Varese", "Lombardia", "Italia") for y in sorted(pop[t])]


def parte_istat(info, args, esiti, problemi, avvisi):
    nome = "istat_popolazione"
    salvato = info.get(nome, {})
    print("ISTAT: controllo la data di aggiornamento…", flush=True)
    agg = ultimo_aggiornamento(FLUSSO_POP)
    ultimo = salvato.get("scaricato")
    vecchio = True
    if ultimo:
        vecchio = (datetime.now(timezone.utc) - datetime.strptime(ultimo, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)).days >= GIORNI_MAX_ISTAT
    if not (args.forza or not os.path.exists(p_pop()) or agg is None or agg != salvato.get("ultimo_aggiornamento_istat") or vecchio):
        salvato["controllato"] = ora()
        info[nome] = salvato
        esiti.append({"parte": nome, "novita": False, "ultimo_anno": salvato.get("ultimo_anno")})
        print(f"ISTAT: nessuna novità (ultimo aggiornamento {agg}).", flush=True)
        return
    print("ISTAT: scarico la popolazione al 1° gennaio…", flush=True)
    time.sleep(PAUSA_ISTAT)
    pop1 = leggi_csv_istat(scarica(url_dati(FLUSSO_POP, f"A.{VARESE}+{REGIONE}+{ITALIA}.JAN.9.TOTAL.99", ANNO_ISTAT_INIZIO), "text/csv", PAUSE_ISTAT_TENTATIVI, "ISTAT"),
                           ["REF_AREA", "TIME_PERIOD", "OBS_VALUE"], "popolazione residente")
    time.sleep(PAUSA_ISTAT)
    pop2 = leggi_csv_istat(scarica(url_dati(FLUSSO_POP_RIC, f"A.{VARESE}+{REGIONE}+{ITALIA}.JAN.TOTAL.9.TOTAL", ANNO_ISTAT_INIZIO), "text/csv", PAUSE_ISTAT_TENTATIVI, "ISTAT"),
                           ["REF_AREA", "TIME_PERIOD", "OBS_VALUE"], "popolazione ricostruita")
    pop = serie_popolazione(pop1, pop2)
    limiti = {"Varese": (600e3, 1.2e6), "Lombardia": (8e6, 11e6), "Italia": (54e6, 63e6)}
    for t, serie in pop.items():
        if not serie:
            raise Problema("formato", f"nei dati ISTAT sulla popolazione manca {t} (codici cambiati?)")
        for y, (v, _) in serie.items():
            if not limiti[t][0] <= v <= limiti[t][1]:
                raise Problema("anomalia", f"popolazione {t} {y} non plausibile: {v:.0f}")
    if len({max(s) for s in pop.values()}) != 1:
        raise Problema("anomalia", "gli ultimi anni di Varese, Lombardia e Italia non coincidono nei dati ISTAT")
    vecchi = carica_pop()
    ultimo_nuovo = max(pop["Varese"])
    ultimo_vecchio = max(vecchi["Varese"]) if vecchi["Varese"] else None
    if ultimo_vecchio and ultimo_nuovo < ultimo_vecchio:
        raise Problema("anomalia", f"i dati ISTAT arrivano al {ultimo_nuovo}, quelli già salvati al {ultimo_vecchio}: tenuti quelli salvati")
    n_nuovo, n_vecchio = sum(len(v) for v in pop.values()), sum(len(v) for v in vecchi.values())
    if n_vecchio and n_nuovo < 0.9 * n_vecchio:
        raise Problema("anomalia", f"i dati ISTAT hanno {n_nuovo} valori, quelli già salvati {n_vecchio}: tenuti quelli salvati")
    cambi = [(t, y, vecchi[t][y][0], pop[t][y][0]) for t in pop for y in pop[t] if y in vecchi[t] and vecchi[t][y][0] != pop[t][y][0]]
    grandi = [c for c in cambi if abs(c[3] / c[2] - 1) > 0.03]
    if grandi and not args.accetta:
        raise Problema("anomalia", "ISTAT ha cambiato di più del 3% alcuni valori già salvati (" +
                       ", ".join(f"{t} {y}: {o:.0f} → {n:.0f}" for t, y, o, n in grandi[:4]) + "): dati NON sostituiti. Verificare e, se giusto, rilanciare con «Accetta»")
    if cambi:
        avvisi.append(f"ISTAT ha rivisto {len(cambi)} valori di popolazione già salvati (variazione massima {max(abs(c[3] / c[2] - 1) for c in cambi) * 100:.2f}%)")
    modificato = scrivi_csv_file(p_pop(), CSV_POP, righe_pop(pop))
    info[nome] = {"scaricato": ora(), "controllato": ora(), "ultimo_anno": ultimo_nuovo, "righe": n_nuovo, "ultimo_aggiornamento_istat": agg,
                  "dati_modificati": ora() if modificato else salvato.get("dati_modificati", ora())}
    esiti.append({"parte": nome, "novita": modificato, "ultimo_anno": ultimo_nuovo, "prima": ultimo_vecchio})
    print(f"ISTAT: {n_nuovo} valori, ultimo anno {ultimo_nuovo}, ultimo aggiornamento {agg}, {'MODIFICATO' if modificato else 'invariato'}", flush=True)


# ---------------------------------------------------------------------------------------------------- principale
def main(argv=None):
    arg = argparse.ArgumentParser(description="Aggiorna i dati delle autovetture (ACI) e della popolazione (ISTAT)")
    arg.add_argument("--esito", help="file JSON in cui scrivere l'esito (lo legge segnala_problemi.py)")
    arg.add_argument("--forza", action="store_true", help="scarica e ricontrolla tutto anche senza novità")
    arg.add_argument("--accetta", action="store_true", help="salva anche se un controllo di plausibilità segnala un'anomalia")
    args = arg.parse_args(argv)
    prova = os.environ.get("PROVA_ERRORE", "").lower() == "true"
    os.makedirs(CARTELLA, exist_ok=True)
    p_info = os.path.join(CARTELLA, "aggiornamento.json")
    info = json.load(open(p_info, encoding="utf-8")) if os.path.exists(p_info) else {}
    problemi, esiti, avvisi = [], [], []
    parti = [("aci", "Autovetture ACI (Autoritratto)", parte_aci),
             ("istat_popolazione", "Popolazione ISTAT", parte_istat)]
    for cod, nome, fn in parti:
        try:
            if prova and cod == parti[-1][0]:
                raise Problema("prova", "errore simulato per provare l'e-mail di avviso (nessun problema reale)")
            fn(info, args, esiti, problemi, avvisi)
        except Problema as e:
            problemi.append({"tavola": cod, "nome": nome, "tipo": e.tipo, "dettaglio": str(e), "ultimo_anno_salvato": info.get(cod, {}).get("anno") or info.get(cod, {}).get("ultimo_anno")})
            print(f"{cod}: PROBLEMA ({e.tipo}) {e}", flush=True)
        except Exception as e:  # imprevisto: lo si segnala come tale
            problemi.append({"tavola": cod, "nome": nome, "tipo": "imprevisto", "dettaglio": f"{type(e).__name__}: {e}",
                             "ultimo_anno_salvato": info.get(cod, {}).get("anno") or info.get(cod, {}).get("ultimo_anno")})
            print(f"{cod}: ERRORE IMPREVISTO {type(e).__name__}: {e}", flush=True)
    info["controllato"] = ora()
    info["avvisi"] = avvisi
    with open(p_info, "w", encoding="utf-8") as f:
        json.dump(info, f, ensure_ascii=False, indent=1)
        f.write("\n")
    if args.esito:
        with open(args.esito, "w", encoding="utf-8") as f:
            json.dump({"quando": info["controllato"], "prova": prova, "problemi": problemi,
                       "tavole": [{"tavola": e["parte"], "nome": e["parte"], "ultimo_anno": e.get("anno") or e.get("ultimo_anno"),
                                   "cambiato": e.get("novita")} for e in esiti], "avvisi": avvisi}, f, ensure_ascii=False, indent=1)
    for a in avvisi:
        print("AVVISO:", a, flush=True)
    if problemi:
        print("\n".join(f"{p['tavola']}: {p['dettaglio']}" for p in problemi), file=sys.stderr)
        if not args.esito:
            sys.exit(1)


if __name__ == "__main__":
    main()
