module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutDefs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3XData

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaHAut

open CFSG.Fischer CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3

@[expose] def d2Tab : Array ℕ := compA 693 dTab dTab

@[expose] def dsTab : Array ℕ := compA 693 dTab sTab

@[expose] def d2sTab : Array ℕ := compA 693 d2Tab sTab

@[expose] def lvL : Array Level := chL.levels

@[expose] def basicCheck : Bool :=
  validA 693 dTab && validA 693 sTab && eqA 693 (compA 693 dTab d2Tab) (idA 693) &&
    eqA 693 (compA 693 sTab sTab) (idA 693) &&
    eqA 693 (compA 693 (compA 693 sTab dTab) (compA 693 sTab dTab)) (idA 693)

@[expose] def normLCheck : Bool :=
  chL.O.all fun g => siftA 693 lvL chL.B 0 (conjA 693 dTab g) &&
    siftA 693 lvL chL.B 0 (conjA 693 sTab g)

@[expose] def outerCheck : Bool :=
  [dTab, d2Tab, sTab, dsTab, d2sTab].all fun x => !(siftA 693 lvL chL.B 0 x)

@[expose] def normBy (c : ChainData) (lv : Array Level) : Bool :=
  c.O.all fun g => siftA 693 lv c.B 0 (conjA 693 dTab g) && siftA 693 lv c.B 0 (conjA 693 sTab g)

@[expose] def normObjCheck : Bool :=
  normBy chS lvS && normBy chX1 lvX1 && normBy chX2 lvX2 && normBy chX3 lvX3 &&
    normBy chK1 lvK1 && normBy chK2 lvK2 && normBy chA1 lvA1 && normBy chA2 lvA2 &&
    normBy chK1A1 lvK1A1 && normBy chK2A2 lvK2A2 && normBy chSJ lvSJ && normBy chA3 lvA3 &&
    normBy chA4 lvA4 && normBy chX8 lvX8 && normBy chSig lvSig && normBy chLam lvLam &&
    normBy chZ2S lvZ2S && normBy chZ lvZ && normBy chX1Z lvX1Z && normBy chP2 lvP2 &&
    normBy chX6Z lvX6Z

@[expose] def dLetters : List ℕ := [0, 1, 4, 11, 12, 13, 14, 15, 17]

@[expose] def sLetters : List ℕ := [0, 2, 4, 5, 7, 9, 11, 12, 14, 15, 16, 17]

@[expose] def sPairs : List ℕ := [0, 2, 5, 7, 9, 12]

@[expose] def letterCheck : Bool :=
  dLetters.all (fun k => eqA 693 (compA 693 dTab (gA k)) (compA 693 (gA k) dTab)) &&
    sLetters.all (fun k => eqA 693 (compA 693 sTab (gA k)) (compA 693 (gA k) sTab)) &&
    sPairs.all fun k => eqA 693 (conjA 693 sTab (gA (k + 1))) (compA 693 (gA k) (gA (k + 1)))

@[expose] def lamWords : List (List ℕ) :=
  [[], [1], [15, 1], [0, 15, 1], [1, 15, 1], [15, 1, 15, 1], [0, 1, 15, 1], [0, 15, 1, 15, 1],
    [15, 0, 1, 15, 1], [0, 15, 0, 1, 15, 1]]

@[expose] def c8Letters : List ℕ := [0, 4, 15, 17, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

@[expose] def l1Words : List (List ℕ) :=
  (lamWords.map fun l => c8Letters.map fun k => l ++ [k] ++ l.reverse).flatten

@[expose] def l1Cands : List (Array ℕ) := l1Words.map wA

@[expose] def noCommonFix (a : Array ℕ) : Bool :=
  let cs := l1Cands.filter fun y => eqA 693 (compA 693 y a) (compA 693 a y)
  allLt 693 fun p => cs.any fun y => y[p]! != p

@[expose] def l1Check : Bool :=
  allLt eA4.pts.size fun i =>
    eqA 693 eA4.pts[i]! (idA 693) ||
      (List.range 5).any (fun k =>
        validA 693 (wA qF[k]!) && eqA 693 eA4.pts[i]! (conjInvA 693 (wA qF[k]!) (gA 14))) ||
      noCommonFix eA4.pts[i]!

@[expose] def p4Check : Bool :=
  allLt eK1.pts.size fun i =>
    !(chA4.O.all fun a => siftA 693 lvA4 chA4.B 0 (conjA 693 eK1.pts[i]! a)) ||
      siftA 693 lvP2 chP2.B 0 eK1.pts[i]!

end CFSG.EvenSmallLie.UnitarySix.YamadaHAut
