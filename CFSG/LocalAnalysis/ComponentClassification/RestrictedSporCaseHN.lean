module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporLocal
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporInputs

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier (fixSub)

theorem not_isSmallOrder_HS : ¬ IsSmallOrder 44352000 :=
  not_isSmallOrder_of_between (q₀ := 445) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem not_isSmallOrder_A10 : ¬ IsSmallOrder 1814400 :=
  not_isSmallOrder_of_between (q₀ := 153) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem orderOf_eq_two_of_mul_self {G : Type*} [Group G] {α : MulAut G} (h2 : α * α = 1)
    (hα : α ∉ inner G) : orderOf α = 2 := by
  refine orderOf_eq_prime (by rw [sq]; exact h2) fun h1 => hα ?_
  rw [h1]
  exact one_mem _

theorem sporadicCase_HN_of_inputs (hin : HNLocalComponentsInput) (hout : FourExactOuterInput) :
    SporadicCase .HN := by
  refine sporadicCase_of_comps (fun G _ _ ⟨e⟩ t ht B hB => ?_)
    (fun G _ _ hs hnab hG α hα2 hα => ?_)
  · refine not_small_of_card_quotient ?_
    rw [hin G e t ht B hB]
    exact not_isSmallOrder_HS
  · obtain ⟨-, -, -, -, ⟨eS⟩, -⟩ :=
      hout G hs hnab (Or.inr (Or.inl hG)) α (orderOf_eq_two_of_mul_self hα2 hα) hα
    refine CompsSatisfy.of_mulEquiv isoInvariant_not_small eS ?_
    refine compsSatisfy_perm_ten.mono fun Y _ h => not_small_of_card_quotient ?_
    rw [Set.mem_singleton_iff.1 h]
    exact not_isSmallOrder_A10

end CFSG.ComponentClassification.RestrictedStd.Spor
