module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Data

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Recognition.HSMultiplier

@[expose] def sigY (i : Fin 6) : Table := wordTbl 11200 harYs (sigWords.getD i.val [])

@[expose] def sigYI (i : Fin 6) : Table := invT 11200 (sigY i)

@[expose] def sigWord (w : List ℕ) : List ℕ := (w.map fun a => sigWords.getD (a - 1) []).flatten

@[expose] def fixCnt (n : ℕ) (T : Table) : ℕ :=
  ((List.finRange n).filter fun i => ap T i.val == i.val).length

@[expose] def outerWord : List ℕ := [3, 4, 5]

@[expose] def sigmaOK : Bool :=
  (List.finRange 6).all (fun i => permOK 11200 (sigY i) && invOK 11200 (sigY i) (sigYI i)) &&
  hsRels.all (fun r => (List.finRange 6).all fun i =>
    commTT 11200 (sigY i) (evalW 11200 sigY sigYI r)) &&
  (List.finRange 6).all (fun i =>
    tblEq 11200 (evalW 11200 sigY sigYI (hsCommWord i)) (sigY i)) &&
  (List.finRange 6).all (fun i =>
    tblEq 11200 (wordTbl 11200 harYs (sigWord (sigWords.getD i.val []))) (harY i)) &&
  fixCnt 11200 (wordTbl 11200 harYs outerWord) !=
    fixCnt 11200 (wordTbl 11200 harYs (sigWord outerWord))

@[expose] def betaT (j : ℕ) : Table := wordTbl 11200 harYs (betaWords.getD j [])

@[expose] def tT : Table := wordTbl 11200 harYs tWord

@[expose] def e1T (a b c u : ℕ) : Table :=
  compT 11200 (compT 11200 (compT 11200 (powT 11200 a (betaT 0)) (powT 11200 b (betaT 1)))
    (powT 11200 c (betaT 2))) (powT 11200 u tT)

@[expose] def e1OK : Bool :=
  (List.range 3).all (fun j =>
    permOK 11200 (betaT j) && invOK 11200 (betaT j) (invT 11200 (betaT j))) &&
  permOK 11200 tT && invOK 11200 tT (invT 11200 tT) && involOK 11200 tT &&
  harYs.all (commTT 11200 tT) &&
  (List.range 3).all (fun i => (List.range 3).all fun j =>
    commTT 11200 (betaT i) (betaT j)) &&
  (List.range 3).all (fun j => tblEq 11200 (powT 11200 4 (betaT j)) (idT 11200)) &&
  (List.range 4).all (fun a => (List.range 4).all fun b => (List.range 4).all fun c =>
    (List.range 2).all fun u =>
      (a == 0 && b == 0 && c == 0 && u == 0) || !tblEq 11200 (e1T a b c u) (idT 11200))

@[expose] def sigBetaT (b j : ℕ) : Table :=
  if b = 0 then betaT j else wordTbl 11200 harYs (sigWord (betaWords.getD j []))

@[expose] def kapT (c : List ℕ) : Table :=
  compT 11200 (compT 11200 (compT 11200 (powT 11200 (c.getD 0 0) (betaT 0))
    (powT 11200 (c.getD 1 0) (betaT 1))) (powT 11200 (c.getD 2 0 / 2) tT))
    (powT 11200 (c.getD 3 0) (betaT 2))

@[expose] def colOf (d : List ℕ) (jj : ℕ) : List ℕ :=
  (List.range 4).map fun i => d.getD (4 * i + jj) 0

@[expose] def realEq (lw : List ℕ) (b : ℕ) (d : List ℕ) (j : ℕ) : Bool :=
  let L := wordTbl 11200 harYs lw
  invOK 11200 L (invT 11200 L) &&
    tblEq 11200 (conjT 11200 L (invT 11200 L) (sigBetaT b j)) (kapT (colOf d ([0, 1, 3].getD j 0)))

@[expose] def realShapeOK (b : ℕ) (d : List ℕ) : Bool :=
  d.length == 16 && d.all (· < 4) && colOf d 2 == [0, 0, if b = 0 then 1 else 3, 0] &&
    (colOf d 0).getD 2 0 % 2 == 0 && (colOf d 1).getD 2 0 % 2 == 0 && (colOf d 3).getD 2 0 % 2 == 0

@[expose] def realOK : Bool :=
  (List.range 3).all (fun j =>
    realEq gamma1Word 0 gamma1Data j && realEq gamma2Word 1 gamma2Data j) &&
  realShapeOK 0 gamma1Data && realShapeOK 1 gamma2Data

@[expose] def piBetaT (j : ℕ) : Table := wordTbl 3850 harXs (betaWords.getD j [])

@[expose] def piBetaSqT (j : ℕ) : Table := compT 3850 (piBetaT j) (piBetaT j)

@[expose] def sigmaPts : List ℕ :=
  (List.range 3850).filter fun p => (List.range 3).all fun j => ap (piBetaSqT j) p == p

@[expose] def orbitStepsStr : String := include_str "S9OrbitSteps.txt"

@[expose] def pairUp : List ℕ → List (ℕ × ℕ)
  | a :: b :: r => (a, b) :: pairUp r
  | _ => []

@[expose] def orbitSteps : List (ℕ × ℕ) :=
  pairUp ((orbitStepsStr.splitOn " ").map String.toNat!)

@[expose] def imgList (T : Table) (l : List ℕ) : List ℕ := l.map (ap T)

@[expose] def orbitStep (acc : Option (Array (List ℕ))) (st : ℕ × ℕ) :
    Option (Array (List ℕ)) :=
  match acc with
  | none => none
  | some a =>
    if h : st.1 < a.size ∧ st.2 < 6 then
      some (a.push (imgList (harXs.getD st.2 (idT 3850)) a[st.1]))
    else none

@[expose] def orbitSets : Option (Array (List ℕ)) :=
  orbitSteps.foldl orbitStep (some #[sigmaPts])

@[expose] def canonList (l : List ℕ) : List ℕ := (List.range 3850).filter fun p => l.contains p

@[expose] def setKey (l : List ℕ) : ℕ := (canonList l).foldr (fun p acc => p + 4096 * acc) 0

@[expose] def orbitOK : Bool :=
  match orbitSets with
  | none => false
  | some a => a.size == 4125 && a.all (fun l => l.all (· < 3850)) &&
      strictlyIncreasing ((a.toList.map setKey).mergeSort)

end CFSG.EvenSporadicStandard.TwoHS
