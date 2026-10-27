module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicCertInputs
public import CFSG.LieType.Multipliers.L34Data
public import CFSG.Certificates.WordSubgroup

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable

@[expose] def wa : List ℕ := [2, 0, 0, 2, 0, 0, 1, 0, 2, 0, 2]

@[expose] def wb : List ℕ := [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0]

@[expose] def aST : Tab := wordTab wa

@[expose] def bST : Tab := wordTab wb

@[expose] def letTab (l : Fin 2 × Bool) : Tab :=
  if l.1 = 0 then (if l.2 then aST else invTab 42 aST) else (if l.2 then bST else invTab 42 bST)

@[expose] def abTab (w : List (Fin 2 × Bool)) : Tab :=
  w.foldl (fun t l => comp 42 t (letTab l)) (idTab 42)

@[expose] def genABWords : List (List (Fin 2 × Bool)) :=
  [parseWord "BabbabaBBabaB", parseWord "BBababbaBBaBabb", parseWord "ababbabaBababbaBa"]

@[expose] def uAU : List (Fin 2 × Bool) := parseWord "BBaBBaBaBBababaBa"

@[expose] def uBU : List (Fin 2 × Bool) := parseWord "baBBaBBa"

@[expose] def uAF : List (Fin 2 × Bool) := parseWord "babbaBaBBaBabaB"

@[expose] def uBF : List (Fin 2 × Bool) := parseWord "aBaBBaBBabb"

@[expose] def uAG : List (Fin 2 × Bool) := parseWord "aBaba"

@[expose] def uBG : List (Fin 2 × Bool) := parseWord "BabaBaBab"

@[expose] def autWs (uA uB : List (Fin 2 × Bool)) : List (List (Fin 2 × Bool)) :=
  [substWord [uA, uB] (commWords (coverPairs 0)), substWord [uA, uB] (commWords (coverPairs 1))]

@[expose] def alphaU (w : List (Fin 2 × Bool)) : List (Fin 2 × Bool) := substWord (autWs uAU uBU) w

@[expose] def alphaF (w : List (Fin 2 × Bool)) : List (Fin 2 × Bool) := substWord (autWs uAF uBF) w

@[expose] def alphaG (w : List (Fin 2 × Bool)) : List (Fin 2 × Bool) := substWord (autWs uAG uBG) w

@[expose] def twStrings : List String :=
    ["", "BaBBabbabbaBBa", "bbaBB", "BaBBaBaBBa", "bbaBababaBBababab", "bababaBBabaBaBaBBa",
     "bababaBBababab", "BabbaBaBabbabaBa", "aBababaBaBBaBabbaBaba", "baBBabaBaBababaBBaba",
     "BababbabbaBabbabbaBa", "ababbabbaBabbabbaba", "baBababaBaBabaB", "bbabaBababb",
     "abbaBaBababaBBa", "BBaBababb", "babbababaBaba", "abaBabbababbaBa", "baBabbabaBaBa",
     "BabaBaBBabbabaBBa", "BabaBaBBaBabbab", "aBaBaBBaBBababb", "aBBaBabbaBababaBa",
     "Babababbabbabb", "BababbaBBaBab", "BaBBaBBaBabbaBBa", "BaBabbababbaBBab", "BaBBaBBabaBBa",
     "baBabbabbaBabababa", "abaBBaBaBBabaBa", "abaBBaBabbaBaBabab", "BabaBBaBabbaBabaBaB",
     "baBabbaBBabaB", "abbaBBababbabbab", "abbaBBababaBBa", "aBabbaBababbaB", "baBaBaBabababa",
     "BBaBabbabbababa", "abababbabaB", "aBabaBBabaBaBaba", "BBaBBaBababbabb",
     "abbababaBaBababaB", "abaBaBabaBBababba", "aBababaBabbaBaba", "BaBBabbabaBaBBabbab",
     "BaBBabbababaBBa", "BabbaBBaBaBBabab", "baBBaBabaBBaba", "bbaBaBabbabaBaBa",
     "aBBababaBBabaBab", "ababaBaBBabaB", "bbaBabaBaBababbaBab", "abbaBabaBBa",
     "abbaBaBaBBabbab", "abbaBaBabbaBBa", "abbaBabbabbab", "bbaBBabababbabaB",
     "baBaBababaBaBaBBa", "baBaBBaBaBa", "BBaBBaBBaBaBab", "BababbaBabaBaBaBab",
     "BabaBabbaBaBabba", "BaBababaBBababbaBa", "abbaBaBBabbabaBab"]

@[expose] def tgWords : List (List ℕ) :=
    [[], [0, 1, 0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 1, 0, 0],
     [0, 1, 0, 2, 1, 0, 0, 1, 0, 0], [1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0],
     [0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0],
     [0, 1, 0, 2, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0],
     [0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0],
     [0, 1, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 1, 0, 0], [0, 1, 0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0],
     [2, 0, 2, 1, 0, 1, 0, 2, 1, 0, 2, 1], [0, 1, 0, 1, 0, 1, 0, 0, 2, 0, 1, 0, 1, 0, 0],
     [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0],
     [0, 1, 0, 2, 0, 1, 0, 0, 2, 1, 0, 1, 0, 1, 0, 0],
     [0, 1, 0, 0, 2, 0, 0, 2, 0, 2, 0, 1, 0, 0], [2, 1, 0, 2, 0, 1, 0, 2, 0, 2],
     [0, 1, 0, 0, 1, 0, 1, 0, 0], [0, 0, 1, 0, 1, 0, 1], [0, 2, 1, 0, 1, 0, 2, 0, 1, 0, 2],
     [0, 2, 0, 1, 0, 2, 1, 0, 1, 0, 2, 1], [0, 1, 0, 0, 2, 1, 0, 1, 0, 0],
     [0, 1, 0, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1], [0, 1, 0, 0, 2, 1, 0, 0, 2, 0, 0, 1, 0, 0],
     [1, 0, 0, 2, 0, 2, 0, 2, 0, 0, 1, 0], [0, 1, 0, 0, 2, 0, 1, 0, 0],
     [0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0],
     [0, 1, 0, 0, 2, 0, 0, 2, 1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1],
     [1, 0, 0, 1, 0, 0, 1, 0], [0, 0, 2, 1, 0, 1, 0, 2, 0, 2, 0, 2],
     [0, 1, 0, 1, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0],
     [0, 1, 0, 1, 0, 2, 0, 1, 0, 0], [2, 0, 2, 0, 2, 1, 0, 2, 0, 2, 0],
     [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2, 0, 0], [0, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 1, 0],
     [0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 0], [0, 1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 1, 0, 0],
     [2, 0, 2, 0, 0, 2, 0, 0, 1, 0, 2, 0, 2], [0, 1, 0, 2, 0, 2, 1, 0, 0, 2, 0, 0, 1, 0, 0],
     [0, 1, 0, 0, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 0],
     [0, 0, 1, 0, 2, 1, 0, 2, 0, 2, 1, 0, 1], [0, 1, 0, 2, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0],
     [2, 1, 0, 0, 2, 1, 0, 2, 0, 2, 0, 2, 0, 0], [0, 1, 0, 2, 0, 2, 0, 1, 0, 0],
     [0, 2, 0, 0, 1, 0, 0, 1, 0, 2, 0, 2], [0, 1, 0, 2, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0],
     [2, 0, 2, 1, 0, 2, 0, 0, 1, 0, 0, 2, 0], [0, 1, 0, 2, 0, 1, 0, 1, 0, 0],
     [0, 1, 0, 2, 0, 0, 1, 0, 1, 0, 1, 0, 1], [2, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 2],
     [0, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 1], [0, 0, 1, 0, 2, 0, 2, 1, 0, 2, 0, 1],
     [0, 1, 0, 2, 1, 0, 2, 0, 1, 0, 0], [0, 1, 0, 1, 0, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0],
     [0, 1, 0, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 0], [0, 2, 0, 1, 0, 1, 0, 0, 2, 0, 0, 2, 0],
     [0, 1, 0, 2, 1, 0, 2, 1, 0, 1, 0, 0], [0, 1, 0, 2, 1, 0, 1, 0, 0, 2, 1, 0, 0, 1, 0, 0],
     [0, 0, 2, 0, 1, 0, 2, 0, 0, 2, 1, 0, 0, 2], [0, 2, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1],
     [0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 0]]

@[expose] def tw (k : ℕ) : List (Fin 2 × Bool) := parseWord (twStrings.getD k "")

@[expose] def tg (k : ℕ) : List ℕ := tgWords.getD k []

@[expose] def twl (ks : List ℕ) : List (Fin 2 × Bool) := (ks.map tw).flatten

@[expose] def witnessF : List (Fin 2 × Bool) := parseWord "bbaBaBBaBabaaabbabbabbabbabbabbabb"

@[expose] def witnessG : List (Fin 2 × Bool) := parseWord "BabaBabaaaabbabbabbabbabbabbabb"

@[expose] def witnessU : List (Fin 2 × Bool) := parseWord "bbaBaBBaBabaaabbabbabbabbabbabbabb"

@[expose] def zword (p q r : ℕ) : List (Fin 2 × Bool) :=
  wpow zOne p ++ wpow zTwo q ++ wpow zThree r

@[expose] def sqData : List (ℕ × ℕ × ℕ × ℕ) :=
    [(1, 0, 0, 2), (2, 1, 0, 2), (3, 1, 0, 0), (4, 1, 1, 1), (5, 0, 1, 1), (6, 1, 0, 2),
     (7, 0, 1, 0), (8, 1, 0, 0), (9, 0, 1, 2), (10, 1, 1, 0), (11, 0, 0, 1), (12, 1, 0, 2),
     (13, 1, 0, 2), (14, 1, 0, 2), (15, 1, 0, 0), (16, 1, 0, 2), (20, 1, 0, 1), (24, 1, 0, 1),
     (28, 0, 0, 1), (32, 1, 0, 1), (36, 1, 0, 2), (40, 1, 0, 1), (44, 1, 0, 2), (48, 0, 1, 0),
     (52, 1, 0, 1), (56, 1, 0, 2), (60, 1, 0, 1)]

@[expose] def commData : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
    [(1, 2, 0, 0, 0), (1, 4, 2, 0, 0), (1, 8, 2, 2, 0), (2, 4, 2, 2, 0), (2, 8, 0, 2, 0),
     (4, 8, 0, 0, 0), (4, 8, 0, 0, 0), (4, 1, 2, 0, 0), (4, 2, 2, 2, 0), (8, 2, 0, 2, 0),
     (8, 1, 2, 2, 0), (12, 1, 0, 2, 0), (12, 2, 2, 0, 0), (4, 1, 2, 0, 0), (4, 3, 0, 2, 0),
     (4, 2, 2, 2, 0)]

@[expose] def unitData : List (ℕ × ℕ × ℕ × ℕ) :=
    [(35, 0, 3, 0), (38, 3, 1, 0)]

@[expose] def fourthData : List (List ℕ × ℕ × ℕ × ℕ) :=
    [([35], 0, 2, 0), ([38], 2, 2, 0), ([35, 38], 2, 0, 0)]

@[expose] def q8Idx : List ℕ := [0, 4, 35, 38, 47, 49, 58, 61]

@[expose] def coverSpecs : List (List (Fin 2 × Bool) × ℕ × ℕ × ℕ) :=
  [(alphaU zOne ++ zOne, 0, 0, 0), (alphaU zTwo ++ zTwo, 0, 0, 0)] ++
    sqData.map (fun d => (wpow (tw d.1) 2, 2 * d.2.1, 2 * d.2.2.1, d.2.2.2)) ++
    commData.map (fun d => (commWord (tw d.1) (tw d.2.1), d.2.2.1, d.2.2.2.1, d.2.2.2.2)) ++
    unitData.map (fun d => (FreeGroup.invRev (tw d.1) ++ alphaU (tw d.1), d.2.1, d.2.2.1,
      d.2.2.2)) ++
    fourthData.map (fun d => (wpow (twl d.1) 4, d.2.1, d.2.2.1, d.2.2.2)) ++
    [(FreeGroup.invRev witnessF ++ alphaF witnessF, 0, 0, 0),
      (wpow witnessF 2, 0, 0, 0),
      (FreeGroup.invRev witnessG ++ alphaG witnessG, 0, 0, 1),
      (wpow witnessG 2, 0, 0, 2),
      (FreeGroup.invRev witnessU ++ alphaU witnessU, 0, 0, 0),
      (wpow witnessU 2, 0, 0, 0)]

@[expose] def coverWalks : List (List (Fin 2 × Bool) × ℕ) :=
  coverSpecs.map fun s => (s.1 ++ FreeGroup.invRev (zword s.2.1 s.2.2.1 s.2.2.2), 1)

@[expose] def witnessOK (w : List (Fin 2 × Bool)) (ρT : Tab) : Bool :=
  comp 42 (abTab w) (abTab w) == idTab 42 && !(abTab w == idTab 42) &&
    comp 42 (abTab w) ρT == comp 42 ρT (abTab w)

@[noinline, expose] def coverTabOK : Bool :=
  let ET := enumBFS 42 (wordTabs wT₀) 64
  let iT := indexOf ET.tabs
  invsOK 42 #[aST, bST] #[invTab 42 aST, invTab 42 bST] &&
    rels.all (fun r => abTab r == idTab 42) &&
    coverWs.all (fun r => abTab r == idTab 42) &&
    (abTab zOne == idTab 42 && abTab zTwo == idTab 42 && abTab zThree == idTab 42) &&
    !(bST == idTab 42) &&
    (abTab (genABWords.getD 0 []) == g₁T && abTab (genABWords.getD 1 []) == g₂T &&
      abTab (genABWords.getD 2 []) == g₃T) &&
    (abTab uAU == conjTab 42 r₄T r₄T aST && abTab uBU == conjTab 42 r₄T r₄T bST) &&
    (abTab uAF == conjTab 42 r₂T r₂T aST && abTab uBF == conjTab 42 r₂T r₂T bST) &&
    (abTab uAG == conjTab 42 r₃T r₃T aST && abTab uBG == conjTab 42 r₃T r₃T bST) &&
    (allBelow 64 fun k => abTab (tw k) == wordTab (tg k) && found iT ET.tabs (wordTab (tg k))) &&
    (allBelow 64 fun k => allBelow k fun l => !(wordTab (tg k) == wordTab (tg l))) &&
    coverSpecs.all (fun s => abTab s.1 == idTab 42) &&
    (allBelow 64 fun k => (comp 42 (wordTab (tg k)) (wordTab (tg k)) == idTab 42) ==
      (k == 0 || (sqData.map (·.1)).contains k)) &&
    (allBelow 64 fun k => found iT ET.tabs (conjTab 42 r₄T r₄T (wordTab (tg k)))) &&
    (allBelow 64 fun k => (comp 42 (wordTab (tg k)) r₄T == comp 42 r₄T (wordTab (tg k))) ==
      q8Idx.contains k) &&
    countBelow 64 (fun k => comp 42 (wordTab (tg k)) (conjTab 42 r₄T r₄T (wordTab (tg k))) ==
      idTab 42) == 8 &&
    (witnessOK witnessF r₂T && witnessOK witnessG r₃T && witnessOK witnessU r₄T)

end CFSG.ComponentClassification.GrSLit.L34Facts
