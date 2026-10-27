module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Check

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def mzRW : List ℕ := [5, 1, 3, 2, 4, 3, 2, 5, 3]

@[expose] def mzAW : List ℕ := [1, 4, 2, 1, 6, 3, 4, 1, 2, 3, 1, 6, 1, 2]

@[expose] def mzPW : List ℕ := [2, 1, 3, 2, 4, 3, 2, 1, 3, 2]

@[expose] def mzRData : List ℕ := [3, 3, 0, 1, 3, 2, 0, 2, 2, 2, 1, 0, 0, 2, 0, 3]

@[expose] def mzEps : List ℕ := [0, 2, 0, 2]

@[expose] def mzEq (u v : List ℕ) : Bool :=
  tblEq 11200 (wordTbl 11200 harYs u) (wordTbl 11200 harYs v)

@[expose] def rptW (w : List ℕ) (k : ℕ) : List ℕ := (List.replicate k w).flatten

@[expose] def betaW (j : ℕ) : List ℕ := betaWords.getD j []

@[expose] def kapW (c : List ℕ) : List ℕ :=
  rptW (betaW 0) (c.getD 0 0) ++ rptW (betaW 1) (c.getD 1 0) ++ rptW tWord (c.getD 2 0 / 2) ++
    rptW (betaW 2) (c.getD 3 0)

@[noinline, expose] def mzOK : Bool :=
  mzEq (mzRW ++ mzRW ++ mzRW) [] && !mzEq mzRW [] &&
  ((List.range 3).all fun j =>
    mzEq (mzRW ++ betaW j) (kapW (colOf mzRData ([0, 1, 3].getD j 0)) ++ mzRW)) &&
  mzEq (mzAW ++ sigWord mzAW) [] &&
  ((List.range 3).all fun j =>
    mzEq (mzAW ++ sigWord (betaW j)) (rptW (betaW j) 3 ++ mzAW)) &&
  mzEq (mzRW ++ mzAW) (mzAW ++ sigWord mzRW) &&
  mzEq (mzPW ++ mzPW ++ mzPW) [] && !mzEq mzPW [] && !mzEq mzPW mzRW &&
  !mzEq mzPW (mzRW ++ mzRW) && mzEq (mzPW ++ mzRW) (mzRW ++ mzPW) &&
  mzEq (mzPW ++ mzAW) (mzAW ++ sigWord mzPW) &&
  mzEq (gamma1Word ++ mzAW) (kapW mzEps ++ mzAW ++ sigWord gamma1Word) &&
  mzEq (gamma2Word ++ sigWord mzAW) (kapW mzEps ++ mzAW ++ sigWord gamma2Word)

end CFSG.EvenSporadicStandard.TwoHS
