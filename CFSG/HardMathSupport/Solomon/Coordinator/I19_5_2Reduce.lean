module

public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem input19_5_2_of_simple
    (hL2 : ∀ (S : Type) [Group S] [Finite S], IsLTwoOddPow S → IsLocallyBalancedAbs 3 2 S)
    (h6 : IsLocallyBalancedAbs 3 2 (alternatingGroup (Fin 6)))
    (h7 : IsLocallyBalancedAbs 3 2 (alternatingGroup (Fin 7)))
    (hM : IsLocallyBalancedAbs 3 2
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group) :
    Input19_5_2 := by
  intro K _ _ _ hcases A _
  refine IsLocallyBalancedAbs.isLocallyBalanced ?_ A
  rcases hcases with h | ⟨hperf, -, ⟨e⟩⟩ | ⟨hperf, -, ⟨e⟩⟩ | ⟨hperf, -, ⟨e⟩⟩
  · exact hL2 K h
  · exact IsLocallyBalancedAbs.of_quotient_center hperf (IsLocallyBalancedAbs.of_mulEquiv e h6)
  · exact IsLocallyBalancedAbs.of_quotient_center hperf (IsLocallyBalancedAbs.of_mulEquiv e h7)
  · exact IsLocallyBalancedAbs.of_quotient_center hperf (IsLocallyBalancedAbs.of_mulEquiv e hM)

end CFSG.HardMathSupport.Solomon.Coordinator
