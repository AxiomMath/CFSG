module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeGlueData
public import Certificates.Data.HePresData
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsTests

public section

namespace CFSG.ComponentClassification.AS81.HeTri

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.AS81.Hexa
open CFSG.ComponentClassification.AS81.HePres.Native

@[expose] def letterA (n : ℕ) (gs : List (Array ℕ)) (l : ℕ) : Array ℕ :=
  if l % 2 = 0 then gs.getD (l / 2) (idA n) else invCand n (gs.getD (l / 2) (idA n))

@[expose] def evalW (n : ℕ) (gs : List (Array ℕ)) (w : List ℕ) : Array ℕ :=
  w.foldl (fun acc l => compA n acc (letterA n gs l)) (idA n)

@[expose] def relsOK (n : ℕ) (gs : List (Array ℕ)) (rels : List (List ℕ)) : Bool :=
  rels.all fun r => eqA n (evalW n gs r) (idA n)

@[expose] def isOrd12 (n : ℕ) (x : Array ℕ) : Bool :=
  eqA n (powN n x 12) (idA n) && !(eqA n (powN n x 6) (idA n)) && !(eqA n (powN n x 4) (idA n))

@[expose] def repE (i k : ℕ) : Array ℕ := heRepE.getD (2 * i + k) #[]
@[expose] def repF (i k : ℕ) : Array ℕ := heRepF.getD (2 * i + k) #[]
@[expose] def pairE (i : ℕ) : List (Array ℕ) := [repE i 0, repE i 1]
@[expose] def pairF (i : ℕ) : List (Array ℕ) := [repF i 0, repF i 1]
@[expose] def heP23L : List (Array ℕ) := eltsK 64 base64 heP23Gens 9216

@[expose] def heCheckSrc : Bool :=
  relsOK 32 heP12CGens heRelsP && relsOK 32 heP13CGens heRelsP &&
    isOrd12 32 (heP12CGens.getD 1 #[]) && isOrd12 32 (heP13CGens.getD 1 #[]) &&
    (heP0L.filter (commN 32 (heP12CGens.getD 1 #[]))).length == 12 &&
    (heP1L.filter (commN 32 (heP13CGens.getD 1 #[]))).length == 12 &&
    heRepE.all (inLN 64 heP12L) && heRepF.all (inLN 64 heP12L)

@[expose] def heCheckClassB : Bool :=
  heP12L.all fun h => !(isOrd12 64 h && (heP12L.filter (commN 64 h)).length == 12) ||
    (List.range 4).any fun i => heP12L.any fun p => eqA 64 (conjA 64 p (repE i 1)) h

@[expose] def heCheckClassC : Bool :=
  (List.range 4).all fun i => heP12L.all fun h => !(relsOK 64 [h, repE i 1] heRelsP) ||
    (List.range 4).any fun i' => heP12L.any fun c =>
      eqA 64 (conjA 64 c (repE i' 0)) h && eqA 64 (conjA 64 c (repE i' 1)) (repE i 1)

@[expose] def heCheckRepF : Bool :=
  (List.range 4).all fun j => decide (heSigmaF.getD j 0 < 4) &&
    inLN 64 heP12L (heConjF.getD j #[]) &&
    eqA 64 (conjA 64 (heConjF.getD j #[]) (repE (heSigmaF.getD j 0) 0)) (repF j 0) &&
    eqA 64 (conjA 64 (heConjF.getD j #[]) (repE (heSigmaF.getD j 0) 1)) (repF j 1)

@[expose] def heCheckNormB : Bool :=
  (heP12L.filter (normsN 64 heBL heB0Gens)).length == 1024 &&
    (List.range 4).all fun i => (heWordsBE ++ heWordsBF).all fun w =>
      inLN 64 heBL (evalW 64 (pairE i) w) && inLN 64 heBL (evalW 64 (pairF i) w)

@[expose] def conjIn23 (x y : Array ℕ) : Bool := heP23L.any fun q => eqA 64 (conjA 64 q x) y

@[expose] def heWitIdx : List (ℕ × ℕ) :=
  ((List.range 4).flatMap fun i => (List.range 4).map fun j => (i, j)).filter fun p =>
    !(p.1 == 0 && p.2 == 0)

@[expose] def heFusOK (k : ℕ) : Bool :=
  let i := (heWitIdx.getD k (0, 0)).1
  let j := (heWitIdx.getD k (0, 0)).2
  let wE1 := heWit.getD (4 * k) []
  let wF1 := heWit.getD (4 * k + 1) []
  let wE2 := heWit.getD (4 * k + 2) []
  let wF2 := heWit.getD (4 * k + 3) []
  let x1 := evalW 64 (pairE i) wE1
  let x2 := evalW 64 (pairE i) wE2
  let y1 := evalW 64 (pairF j) wF1
  let y2 := evalW 64 (pairF j) wF2
  eqA 32 (evalW 32 heP12CGens wE1) (evalW 32 heP13CGens wF1) &&
    eqA 32 (evalW 32 heP12CGens wE2) (evalW 32 heP13CGens wF2) &&
    eqA 32 (evalW 32 heP13CGens wE1) (evalW 32 heP12CGens wF1) &&
    eqA 32 (evalW 32 heP13CGens wE2) (evalW 32 heP12CGens wF2) &&
    if heWitE.getD k true then conjIn23 x1 x2 && !(conjIn23 y1 y2)
    else conjIn23 y1 y2 && !(conjIn23 x1 x2)

@[expose] def heCheckFus : Bool := (List.range 15).all heFusOK

@[expose] def piIdx (c k : ℕ) : ℕ := if k < 4 then k else c

@[expose] def heCheckPi : Bool :=
  (List.range 5).all (fun k =>
    eqA 64 (evalW 64 (pairE 0) (heWordsE.getD k [])) (hePiEArrs.getD (piIdx 4 k) #[]) &&
      eqA 64 (evalW 64 (pairF 0) (heWordsF.getD k [])) (hePiFArrs.getD (piIdx 5 k) #[]) &&
      eqA 32 (evalW 32 heP12CGens (heWordsE.getD k [])) ((hePiCArrs false).getD (piIdx 4 k) #[]) &&
      eqA 32 (evalW 32 heP13CGens (heWordsF.getD k [])) ((hePiCArrs false).getD (piIdx 5 k) #[]) &&
      eqA 32 (evalW 32 heP13CGens (heWordsE.getD k [])) ((hePiCArrs true).getD (piIdx 4 k) #[]) &&
      eqA 32 (evalW 32 heP12CGens (heWordsF.getD k [])) ((hePiCArrs true).getD (piIdx 5 k) #[])) &&
    (List.range 4).all fun k =>
      eqA 32 (evalW 32 heP12CGens (heWordsBE.getD k [])) (heBCGens.getD k #[]) &&
        eqA 32 (evalW 32 heP13CGens (heWordsBF.getD k [])) (heBCGens.getD k #[])

@[expose] def heT8 (hx hy : Array ℕ) : List (Array ℕ) :=
  (hePiFArrs.toList.take 4) ++ [idA 64, idA 64, hx, hy]

@[expose] def heRels23 : List (List ℕ) := hePiR23Codes

@[expose] def heRelsX : List (List ℕ) :=
  heRels23.filter fun r => r.all fun l => l / 2 < 4 || l / 2 == 6

@[expose] def heRelsY : List (List ℕ) :=
  heRels23.filter fun r => r.all fun l => l / 2 < 4 || l / 2 == 7

@[expose] def heCheckKer : Bool :=
  let xF := hePiFArrs.getD 6 #[]
  let yF := hePiFArrs.getD 7 #[]
  let xF' := conjA 64 hexaT0 xF
  let yF' := conjA 64 hexaT0 yF
  relsOK 64 hePiEArrs.toList hePiRels23Codes &&
    heP23L.all (fun hy => !(relsOK 64 (heT8 (idA 64) hy) heRelsY) || eqA 64 hy yF ||
      eqA 64 hy yF') &&
    heP23L.all fun hx => !(relsOK 64 (heT8 hx (idA 64)) heRelsX) ||
      ((!(relsOK 64 (heT8 hx yF) heRels23) || eqA 64 hx xF) &&
        (!(relsOK 64 (heT8 hx yF') heRels23) || eqA 64 hx xF'))

@[expose] def heCheckValid : Bool :=
  (heRepE ++ heRepF ++ heConjF ++ hePiEArrs.toList ++ hePiFArrs.toList).all (validA 64) &&
    ((hePiCArrs false).toList ++ (hePiCArrs true).toList).all (validA 32) && validA 64 (idA 64) &&
    validA 64 hexaT0 && validA 64 (conjA 64 hexaT0 (hePiFArrs.getD 6 #[])) &&
    validA 64 (conjA 64 hexaT0 (hePiFArrs.getD 7 #[])) && heRepE.length == 8 &&
    heRepF.length == 8 && heConjF.length == 4 &&
    hePiEArrs.size == 8 && hePiFArrs.size == 8 && (hePiCArrs false).size == 8 &&
    (hePiCArrs true).size == 8

@[expose] def heCheckRange : Bool :=
  (heRelsP ++ heWordsE ++ heWordsF ++ heWordsBE ++ heWordsBF ++ heWit).all (·.all (· < 4)) &&
    hePiRels23Codes.all (·.all fun l => l < 8 || l / 2 == 6 || l / 2 == 7) &&
    (heGenWordsC0 ++ heGenWordsC1).all (·.all (· < 12)) &&
    (heGenWordsT ++ heGenWordsM ++ heGenWordsR).all
      (·.all fun l => l < 10 || l / 2 == 6 || l / 2 == 7)

@[expose] def heCheckMem : Bool :=
  (List.range 4).all (fun k => inLN 64 heBL (hePiEArrs.getD k #[]) &&
      inLN 64 heBL (hePiFArrs.getD k #[]) && inLN 32 heBCL ((hePiCArrs false).getD k #[]) &&
      inLN 32 heBCL ((hePiCArrs true).getD k #[])) &&
    inLN 64 heP12L (hePiEArrs.getD 4 #[]) && inLN 64 heP12L (hePiFArrs.getD 5 #[]) &&
    inLN 32 heP0L ((hePiCArrs false).getD 4 #[]) && inLN 32 heP1L ((hePiCArrs false).getD 5 #[]) &&
    inLN 32 heP1L ((hePiCArrs true).getD 4 #[]) && inLN 32 heP0L ((hePiCArrs true).getD 5 #[]) &&
    [6, 7].all fun k =>
      inLN 64 heP23L (hePiEArrs.getD k #[]) && inLN 64 heP23L (hePiFArrs.getD k #[])

@[expose] def heCheckZ : Bool :=
  eqA 32 (evalW 32 (hePiCArrs false).toList [2, 4, 2, 4]) heTCArr &&
    eqA 32 (evalW 32 (hePiCArrs true).toList [2, 4, 2, 4]) heTCArr

@[expose] def heCheckGen : Bool :=
  heGenWordsC0.length == hePCGens.length && heGenWordsC1.length == hePCGens.length &&
    heGenWordsT.length == hexaTGens.length && heGenWordsM.length == hexaMGens.length &&
    (List.range hePCGens.length).all (fun k =>
      eqA 32 (evalW 32 (hePiCArrs false).toList (heGenWordsC0.getD k [])) (hePCGens.getD k #[]) &&
        eqA 32 (evalW 32 (hePiCArrs true).toList (heGenWordsC1.getD k [])) (hePCGens.getD k #[])) &&
    (List.range hexaTGens.length).all (fun k =>
      eqA 64 (evalW 64 hePiEArrs.toList (heGenWordsT.getD k [])) (hexaTGens.getD k #[])) &&
    (List.range hexaMGens.length).all (fun k =>
      eqA 64 (evalW 64 hePiEArrs.toList (heGenWordsM.getD k [])) (hexaMGens.getD k #[])) &&
    heGenWordsR.length == hexaR0Gens.length &&
    (List.range hexaR0Gens.length).all fun k =>
      eqA 64 (evalW 64 hePiEArrs.toList (heGenWordsR.getD k [])) (hexaR0Gens.getD k #[])

@[expose] def heGlueCheck : Bool :=
  heCheckValid && heCheckRange && heCheckSrc && heCheckClassB && heCheckClassC && heCheckRepF &&
    heCheckNormB && heCheckFus && heCheckPi && heCheckKer && heCheckMem && heCheckZ && heCheckGen

end CFSG.ComponentClassification.AS81.HeTri
