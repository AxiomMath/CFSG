module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.J3
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.McL

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem sporadicOnePairHolds_J3
    (hB : Nonempty (NativeSporadic.Carrier .J3 ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) :
    SporadicOnePairHolds .J3 3 := by
  refine ⟨fun S _ _ _ ⟨e⟩ => ?_, fun S _ _ _ ⟨e⟩ => ?_⟩
  · exact oPrimeCoreTrivialAt_J3 S ⟨e.trans hB.some⟩
  · exact noOuterFixesCentralizer_J3 S ⟨e.trans hB.some⟩

theorem sporadicOnePairHolds_McL :
    SporadicOnePairHolds .McL 3 := by
  refine ⟨fun S _ _ _ ⟨e⟩ => ?_, fun S _ _ _ ⟨e⟩ => ?_⟩
  · exact OPrimeCoreTrivialAt.of_mulEquiv e oPrimeCoreTrivialAt_McL
  · exact NoOuterFixesCentralizer.of_mulEquiv e noOuterFixesCentralizer_McL

theorem sporadicLocalOnePairs_of_rest
    (hB : SporadicBridges) (hOut : SporadicOuterLeTwo) (h : SporadicOneRest) :
    SporadicLocalOnePairs :=
  sporadicLocalOnePairs_of_parts hB hOut
    (h.toParts (sporadicOnePairHolds_J3 (hB .J3)) sporadicOnePairHolds_McL)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
