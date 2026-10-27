module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open Subgroup CFSG.LocalAnalysis.ComponentInitial

@[expose] def KGNoncycCentL34 : Prop :=
  ∀ (n k : ℕ) (F : Type) [Field F] [Finite F], (n = 3 ∨ n = 4) → Nat.card F = 4 ^ k →
    ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ S B : Subgroup (MulAut (LinearFlag.projectiveSL n F)), IsPGroup 2 ↥S → ¬ IsCyclic ↥S →
      S ⊓ (MulAut.conj : LinearFlag.projectiveSL n F →* MulAut (LinearFlag.projectiveSL n F)).range
        = ⊥ → IsPGroup p ↥B →
      B ≤ normalizer (S : Set (MulAut (LinearFlag.projectiveSL n F))) →
      ∃ σ₁ σ₂ : MulAut (LinearFlag.projectiveSL n F), σ₁ ∈ S ∧ σ₂ ∈ S ∧ σ₁ ≠ 1 ∧ σ₂ ≠ 1 ∧
        (∀ τ ∈ S, τ * σ₁ = σ₁ * τ) ∧ (∀ τ ∈ S, τ * σ₂ = σ₂ * τ) ∧
        (∀ τ ∈ B, τ * σ₁ = σ₁ * τ) ∧ (∀ τ ∈ B, τ * σ₂ = σ₂ * τ) ∧
        Subgroup.closure ({x : LinearFlag.projectiveSL n F | σ₁ x = x} ∪
          {x : LinearFlag.projectiveSL n F | σ₂ x = x}) = ⊤

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
