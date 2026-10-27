module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporAssemble
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Five
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem b3SporPair_Fi24Prime_five
    (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) :
    B3SporPair .Fi24Prime 5 :=
  b3SporPair_of_sporadicOPrimeHolds (by norm_num) (by norm_num) hbr hOut
    sporadicOPrimeHolds_Fi24_five

theorem b3SporPair_Fi24Prime_seven
    (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) : B3SporPair .Fi24Prime 7 :=
  b3SporPair_of_sporadicOPrimeHolds (by norm_num) (by norm_num) hbr hOut
    sporadicOPrimeHolds_Fi24_seven

end CFSG.HardMathSupport.Solomon.Coordinator
