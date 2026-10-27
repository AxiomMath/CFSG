module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open Subgroup

@[expose] def KGNoncycCent : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p → IsSimpleGroup K →
    (∃ x y : K, x * y ≠ y * x) → CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 K →
    ∀ S B : Subgroup (MulAut K), IsPGroup 2 ↥S → ¬ IsCyclic ↥S →
      S ⊓ (MulAut.conj : K →* MulAut K).range = ⊥ → IsPGroup p ↥B →
      B ≤ normalizer (S : Set (MulAut K)) →
      ∃ σ₁ σ₂ : MulAut K, σ₁ ∈ S ∧ σ₂ ∈ S ∧ σ₁ ≠ 1 ∧ σ₂ ≠ 1 ∧
        (∀ τ ∈ S, τ * σ₁ = σ₁ * τ) ∧ (∀ τ ∈ S, τ * σ₂ = σ₂ * τ) ∧
        (∀ τ ∈ B, τ * σ₁ = σ₁ * τ) ∧ (∀ τ ∈ B, τ * σ₂ = σ₂ * τ) ∧
        Subgroup.closure ({k : K | σ₁ k = k} ∪ {k : K | σ₂ k = k}) = ⊤

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
