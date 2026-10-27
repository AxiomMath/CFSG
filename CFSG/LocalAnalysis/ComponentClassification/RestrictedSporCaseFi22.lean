module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporInputs
public import CFSG.Sporadic.FischerOddCore.Fi22LocalComp

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.OuterAutomorphisms

theorem not_isSmallOrder_U62 : ¬ IsSmallOrder 9196830720 :=
  not_isSmallOrder_of_between (q₀ := 2639) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem not_isSmallOrder_O8plus2 : ¬ IsSmallOrder 174182400 :=
  not_isSmallOrder_of_between (q₀ := 703) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem not_isSmallOrder_Sp62 : ¬ IsSmallOrder 1451520 :=
  not_isSmallOrder_of_between (q₀ := 142) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sporadicCase_Fi22_of_inputs (hout : Fi22OuterComponentsInput) : SporadicCase .Fi22 := by
  refine sporadicCase_of_comps (fun G _ _ ⟨e⟩ t ht B hB => ?_)
    (fun G _ _ _ _ hG α hα2 hα B hB => ?_)
  · refine not_small_of_card_quotient ?_
    rw [CTI_Fi22_involution_local_components_unitary_quotient_order e t ht B hB]
    exact not_isSmallOrder_U62
  · refine not_small_of_card_quotient ?_
    rcases hout G hG α hα2 hα B hB with h | h <;> rw [h]
    · exact not_isSmallOrder_O8plus2
    · exact not_isSmallOrder_Sp62

end CFSG.ComponentClassification.RestrictedStd.Spor
