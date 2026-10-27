module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs

public section

namespace CFSG.ComponentClassification.Burgoyne

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.TBLit CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancingLocal
open scoped MatrixGroups

@[expose] def BurgoynePropBE7S : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n p f : ℕ), p ≠ 2 → LieModel S .E7 n p f →
    ∀ v : MulAut S, orderOf v = 2 → ∀ R : Subgroup S, R ≤ autFixed v →
      IsPComponent 2 (R.subgroupOf (autFixed v)) →
    ∀ (p₁ n₁ : ℕ) [Fact p₁.Prime], p₁ ≠ 2 → 0 < n₁ →
    ∀ (N : Subgroup R) [N.Normal], Odd (Nat.card N) →
      Nonempty (R ⧸ N ≃* PSL(2, GaloisField p₁ n₁)) → False

@[expose] def BurgoynePropBClassicalS : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (τ : StatedLieTag) (n p f : ℕ),
    ((τ = .PSL ∨ τ = .PSU) ∧ 6 ≤ n ∧ Even n) ∨ (τ = .PSp ∧ 3 ≤ n) → p ≠ 2 →
    LieModel S τ n p f → ∀ v : MulAut S, orderOf v = 2 → ∀ R : Subgroup S, R ≤ autFixed v →
      IsPComponent 2 (R.subgroupOf (autFixed v)) →
    ∀ (p₁ n₁ : ℕ) [Fact p₁.Prime], p₁ ≠ 2 → 0 < n₁ →
    ∀ (N : Subgroup R) [N.Normal], Odd (Nat.card N) →
      Nonempty (R ⧸ N ≃* PSL(2, GaloisField p₁ n₁)) → False

end CFSG.ComponentClassification.Burgoyne
