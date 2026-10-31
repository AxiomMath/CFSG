module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsDecompP
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsDecompIH
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsCocycle
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsTransversalData

@[expose] public section

namespace CFSG.ComponentClassification.M12Cover.InternalSylow

set_option compiler.extract_closed false

def b64 (c : Char) : ℕ :=
  if c.toNat = 43 then 62 else if c.toNat = 47 then 63 else if c.toNat ≤ 57 then c.toNat - 48
  else if c.toNat ≤ 90 then c.toNat - 55 else c.toNat - 61

def decodeAux (k : ℕ) : List Char → ℕ → ℕ → Array ℕ → Array ℕ
  | [], _, _, acc => acc
  | c :: cs, cnt, cur, acc =>
    if cnt + 1 = k then decodeAux k cs 0 0 (acc.push (cur * 64 + b64 c))
    else decodeAux k cs (cnt + 1) (cur * 64 + b64 c) acc

def decodeB64 (k : ℕ) (s : String) : Array ℕ := decodeAux k s.toList 0 0 #[]

@[irreducible] def parArr : Array ℕ := decodeB64 2 parStr

@[irreducible] def letArr : Array ℕ := decodeB64 1 letStr

@[irreducible] def act1Arr : Array ℕ := decodeB64 2 act1Str

@[irreducible] def act2Arr : Array ℕ := decodeB64 2 act2Str

@[irreducible] def wit1Arr : Array ℕ := decodeB64 1 wit1Str

@[irreducible] def wit2Arr : Array ℕ := decodeB64 1 wit2Str

@[irreducible] def aArr : Array ℕ := decodeB64 1 aStr

@[irreducible] def sigArr : Array ℕ := decodeB64 2 sigStr

@[irreducible] def pArr : Array ℕ := decodeB64 1 pStr

@[irreducible] def ihArr : Array ℕ := decodeB64 2 ihStr

def tpar (i : ℕ) : ℕ := parArr[i]!

def tlet (i : ℕ) : ℕ := letArr[i]!

def tact (l i : ℕ) : ℕ := if l = 1 then act1Arr[i]! else act2Arr[i]!

def twit (l i : ℕ) : ℕ := if l = 1 then wit1Arr[i]! else wit2Arr[i]!

def taIdx (i : ℕ) : ℕ := aArr[i]!

def tsig (i : ℕ) : ℕ := sigArr[i]!

def tp (i h : ℕ) : ℕ := pArr[64 * i + h]!

def tih (i h : ℕ) : ℕ := ihArr[64 * i + h]!

def r0CodeAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, p => p
  | n + 1, i, p => if i = 0 then p else r0CodeAux n (tpar i) (letterCode (tlet i) p)

def r0βCodeAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, p => p
  | n + 1, i, p => if i = 0 then p else r0βCodeAux n (tpar i) (letterCodeβ (tlet i) p)

def gβInvCode : List ℕ := [8, 11, 1, 9, 7, 6, 4, 2, 3, 5, 10, 0]

def rCode (i p : ℕ) : ℕ :=
  wordCode gWord (r0CodeAux 1485 i (SylowTable.nth 0 gInvCode p))

def rβCode (i p : ℕ) : ℕ :=
  wordCodeβ gWord (r0βCodeAux 1485 i (SylowTable.nth 0 gβInvCode p))

@[irreducible] def rCodeArr : Array ℕ :=
  ((List.range (1485 * 12)).map fun k => rCode (k / 12) (k % 12)).toArray

def rCodeCheck : Bool :=
  (List.range 1485).all fun i => (List.range 12).all fun p => rCodeArr[12 * i + p]! == rCode i p

def cosetCheck : Bool :=
  (List.range 1485).all fun i =>
    (i == 0 || (decide (tpar i < i) && (tlet i == 1 || tlet i == 2))) &&
      [1, 2].all fun l => decide (tact l i < 1485) && decide (twit l i < 64) &&
        (List.range 12).all fun p =>
          r0CodeAux 1485 i (letterCode l p) ==
            SylowTable.nth 0 (SylowTable.code (twit l i)) (r0CodeAux 1485 (tact l i) p)

def decompCheck : Bool :=
  (List.range 1485).all fun i => (List.range 64).all fun h =>
    decide (tp i h < 64) && decide (tih i h < 1485) &&
      (List.range 12).all fun p =>
        rCodeArr[12 * i + dCode h p]! == dCode (tp i h) rCodeArr[12 * tih i h + p]!

def betaCheck : Bool :=
  ((List.range 1485).map tsig).Nodup &&
    (List.range 1485).all fun i => decide (taIdx i < 64) && decide (tsig i < 1485) &&
      (List.range 12).all fun p => rβCode i p == dCode (taIdx i) rCodeArr[12 * tsig i + p]!

def quotCheck : Bool :=
  (List.range 1485).all fun i => (List.range 64).all fun h =>
    mIdx (mIdx (invIdx (taIdx i)) (bIdx (tp i h))) (taIdx (tih i h)) == tp (tsig i) (bIdx h)

def FSum (h k : ℕ) : ℕ :=
  ((List.range 1485).map fun i => fIdx (tp i h) (tp (tih i h) k)).sum

def transferCheck : Bool :=
  (List.range 64).all fun h => (List.range 64).all fun k =>
    (FSum h k + muIdx h + muIdx k + muIdx (mIdx h k)) % 2 == fIdx h k

def cIdx (i h : ℕ) : ℕ :=
  fIdx (taIdx i) (invIdx (taIdx i)) + lam0Idx (tp i h) +
    fIdx (invIdx (taIdx i)) (bIdx (tp i h)) +
    fIdx (mIdx (invIdx (taIdx i)) (bIdx (tp i h))) (taIdx (tih i h))

def LamSum (h : ℕ) : ℕ := ((List.range 1485).map fun i => cIdx i h).sum

def lambdaCheck : Bool :=
  (List.range 64).all fun h => (LamSum h + muIdx h + muIdx (bIdx h)) % 2 == lamIdx h

end CFSG.ComponentClassification.M12Cover.InternalSylow
