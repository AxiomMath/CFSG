module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RSporComps
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseB
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms

namespace L34R

theorem not_isL34Type_B
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier .B) {σ : MulAut S} {P : Subgroup S}
    (h : CatLeaf.ProperFixedComponent σ P) : ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
  refine not_isL34Type_of_comps BMCase.sporadicOddCoreFree_B (fun G _ _ ⟨e⟩ t ht K hK => ?_)
    (outer_of_forall_inner fun α => ?_) hna e h
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

end L34R

end CFSG.ComponentClassification.GrSLit
