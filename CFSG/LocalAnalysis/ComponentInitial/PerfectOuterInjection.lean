module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification OuterAutomorphisms

theorem perfect_central_outer_injection (H : Type*) [Group H] (hH : Group.IsPerfect H) :
    (∃ φ : Outer H →* Outer (H ⧸ center H), Function.Injective φ ∧
      ∀ α : MulAut H, φ (QuotientGroup.mk α) =
        QuotientGroup.mk (PerfectAutomorphisms.centerQuotientHom H α)) ∧
      (Group.IsSolvable (Outer (H ⧸ center H)) → Group.IsSolvable (Outer H)) := by
  refine ⟨⟨centerQuotientOuterHom H, centerQuotient_outer_injective H, fun α => rfl⟩,
    fun hsolv => ?_⟩
  exact solvable_of_centerQuotient H

end CFSG.LocalAnalysis.ComponentInitial
