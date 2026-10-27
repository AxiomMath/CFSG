module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseFi22
public import CFSG.Sporadic.FischerOddCore.Fi24Block

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.OuterAutomorphisms

theorem not_isSmallOrder_Fi22 : ¬ IsSmallOrder 64561751654400 :=
  not_isSmallOrder_of_between (q₀ := 50543) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem not_isSmallOrder_Fi23 : ¬ IsSmallOrder 4089470473293004800 :=
  not_isSmallOrder_of_between (q₀ := 2014801) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem sporadicCase_Fi24prime_of_inputs (hout : Fi24primeOuterComponentsInput) :
    SporadicCase .Fi24Prime := by
  refine sporadicCase_of_comps (fun G _ _ ⟨e⟩ t ht B hB => ?_)
    (fun G _ _ _ _ hG α hα2 hα B hB => ?_)
  · refine not_small_of_card_quotient ?_
    rw [(CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven e t ht B
      hB).1]
    exact not_isSmallOrder_Fi22
  · refine not_small_of_card_quotient ?_
    rcases hout G hG α hα2 hα B hB with h | h <;> rw [h]
    · exact not_isSmallOrder_Fi23
    · exact not_isSmallOrder_U62

end CFSG.ComponentClassification.RestrictedStd.Spor
