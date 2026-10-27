module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGL34Defs
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open Subgroup

@[expose] def KGConcl (K : Type) [Group K] (p : ℕ) : Prop :=
  ∀ S B : Subgroup (MulAut K), IsPGroup 2 ↥S → ¬ IsCyclic ↥S →
    S ⊓ (MulAut.conj : K →* MulAut K).range = ⊥ → IsPGroup p ↥B →
    B ≤ normalizer (S : Set (MulAut K)) →
    ∃ σ₁ σ₂ : MulAut K, σ₁ ∈ S ∧ σ₂ ∈ S ∧ σ₁ ≠ 1 ∧ σ₂ ≠ 1 ∧
      (∀ τ ∈ S, τ * σ₁ = σ₁ * τ) ∧ (∀ τ ∈ S, τ * σ₂ = σ₂ * τ) ∧
      (∀ τ ∈ B, τ * σ₁ = σ₁ * τ) ∧ (∀ τ ∈ B, τ * σ₂ = σ₂ * τ) ∧
      Subgroup.closure ({k : K | σ₁ k = k} ∪ {k : K | σ₂ k = k}) = ⊤

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
