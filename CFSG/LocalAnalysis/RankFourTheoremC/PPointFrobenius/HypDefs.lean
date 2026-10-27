module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

@[expose] def MovesHyperplanes {J : Type*} [Group J] (p : ℕ) (U : Subgroup J) (σ : J) : Prop :=
  σ ∈ Subgroup.normalizer (U : Set J) ∧ ∀ j : ℕ, 1 ≤ j → j ≤ 3 → ∀ H : Subgroup J, H ≤ U →
    Nat.card U = p * Nat.card H → ∃ h ∈ H, σ ^ j * h * (σ ^ j)⁻¹ ∉ H

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
