module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocalCheck
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocalData
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpInputs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThreeInputs
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocalCheck
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocalData
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpInputs
public meta import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThreeInputs
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabThNative

open CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative

set_option compiler.extract_closed false

@[expose] def progU : List Op := [
  .mul 0 1 2, .mul 2 1 3, .pow 4 2 4, .mul 4 1 5, .mul 5 3 6, .mul 3 3 7, .mul 7 7 8, .mul 4 7 9,
  .mul 8 9 10, .pow 3 8 11, .mul 11 4 12, .mul 10 11 13, .pow 18 13 14, .mul 14 0 15, .mul 15 13 16,
  .pow 19 12 17, .mul 17 6 18, .mul 18 12 19, .mul 16 19 20, .mul 19 16 21, .pow 10 20 22
  ]

@[expose] def nU : Nat := 23

@[expose] def regsU (_ : Unit := ()) : Array (Array V4) :=
  slpRows (rowsOf seedA) (rowsOf seedB) nU progU


open CFSG.RankThree.PartTwo.Sec4.Item434SporTh CFSG.RankThree.PartTwo.Sec4.Item434SporE81
  CFSG.Monster.B.Fischer CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocal

@[expose] def abcWord (s : String) : List Nat :=
  s.toList.map fun ch => if ch = 'a' then 0 else if ch = 'b' then 1 else 2

@[expose] def abcRows (A B : Mat) (s : String) : Mat :=
  wordRowsL #[A, B, mulRows B B] (abcWord s)

@[expose] def clsRows (Z S U : Mat) (i : Nat) : Mat :=
  if i = 0 then Z else if i = 1 then mulRows Z Z else if i = 2 then S
  else if i = 3 then mulRows S S else if i = 4 then U else mulRows U U

@[expose] def censusFusOK (X : ThLocalData) (data : List (Nat × Nat × String)) (A B Z S U : Mat)
    (M : Nat → Mat) : Bool :=
  X.tgts.all (fun y => data.any (fun d => d.1 == y.1)) &&
    data.all (fun d => decide (d.1 < qN) && decide (d.2.1 < 6) && X.tgts.any (fun y => y.1 == d.1) &&
      let W := abcRows A B d.2.2
      mulRows W (M d.1) == mulRows (clsRows Z S U d.2.1) W)

@[expose] def thCensusCheck (data : List (Nat × Nat × String)) (A B S U : Mat) : Bool :=
  let gs : Array Mat := #[evalWord #[A, B] thE81.w61, evalWord #[A, B] thE81.w62]
  let P : Array Mat := thE81.pW.map (evalWord gs)
  let c := orbCert (tabsOf P) thE81.v thE81.fuel
  thLocalChecks thE81 thLocal A B (zRows ()) gs P c &&
    censusFusOK thLocal data A B (zRows ()) S U (matOf P c.par c.lab qN)

end CFSG.HardMathSupport.Dickson.I271.TabThNative
