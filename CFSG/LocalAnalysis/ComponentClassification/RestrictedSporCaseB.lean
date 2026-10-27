module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseBabySchreier
public import CFSG.Monster.B.CTIB.ComponentsSeventeen

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem not_isSmallOrder_twoE62 : ¬ IsSmallOrder 76532479683774853939200 :=
  not_isSmallOrder_of_between (q₀ := 53492380) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem not_isSmallOrder_F42 : ¬ IsSmallOrder 3311126603366400 :=
  not_isSmallOrder_of_between (q₀ := 187788) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem sporadicCase_B : SporadicCase .B := by
  refine sporadicCase_of_comps (fun G _ _ ⟨e⟩ t ht K hK => ?_)
    (outer_of_forall_inner fun α => ?_)
  · obtain ⟨-, hiso, -⟩ :=
      Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen ⟨e⟩ t ht K
        hK
    refine not_small_of_card_quotient ?_
    rcases hiso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · rw [Nat.card_congr φ.toEquiv, LieType.Chevalley.C2E6Std.card_stdGroup]
      exact not_isSmallOrder_twoE62
    · obtain ⟨ψ⟩ := Monster.B.E6.StdF4Radical.nonempty_groupJ_mulEquiv_F4
      rw [Nat.card_congr φ.toEquiv, ← Nat.card_congr ψ.toEquiv,
        Monster.B.E6.FieldInvF4.card_groupJ]
      exact not_isSmallOrder_F42
  · have h : ∀ β : MulAut (NativeSporadic.Carrier .B),
        β ∈ inner (NativeSporadic.Carrier .B) :=
      BMCase.inner_of_mulEquiv_pinnedB NativeSporadic.B ⟨MulEquiv.refl NativeSporadic.B⟩
    exact h α

end CFSG.ComponentClassification.RestrictedStd.Spor
