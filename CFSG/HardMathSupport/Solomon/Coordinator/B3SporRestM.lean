module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporAssemble
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteen

public section


namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem b3SporPair_M_eleven (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) :
    B3SporPair .M 11 :=
  b3SporPair_of_sporadicOPrimeHolds (by norm_num) (by norm_num) hbr hOut
    sporadicOPrimeHolds_M_eleven

theorem b3SporPair_M_thirteen (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) :
    B3SporPair .M 13 :=
  b3SporPair_of_sporadicOPrimeHolds (by norm_num) (by norm_num) hbr hOut
    (sporadicOPrimeHolds_M_thirteen_of bThirteenOddCore_holds)

end CFSG.HardMathSupport.Solomon.Coordinator
