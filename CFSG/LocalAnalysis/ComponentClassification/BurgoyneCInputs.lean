module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneInputs

public section

namespace CFSG.ComponentClassification.Burgoyne

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.TBLit CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def BurgoyneExcPropCInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (τ : StatedLieTag) (n' p' f' : ℕ), τ ∈ oddExceptionalTags → τ ≠ .G2 → p' ≠ 2 →
      LieModel K τ n' p' f' →
    ∀ x : K, orderOf x = 2 → ∀ R₁ R₂ : Subgroup K,
      R₁ ≤ centralizer ({x} : Set K) → IsPComponent 2 (R₁.subgroupOf (centralizer ({x} : Set K))) →
      R₂ ≤ centralizer ({x} : Set K) → IsPComponent 2 (R₂.subgroupOf (centralizer ({x} : Set K))) →
    ∀ (p n : ℕ) [Fact p.Prime], p ≠ 2 → 0 < n →
      Nonempty (R₁ ⧸ pPrimeCore 2 R₁ ≃* PSL(2, GaloisField p n)) →
      Nonempty (R₂ ⧸ pPrimeCore 2 R₂ ≃* SL(2, GaloisField p n)) → x ∈ R₂ → False

end CFSG.ComponentClassification.Burgoyne
