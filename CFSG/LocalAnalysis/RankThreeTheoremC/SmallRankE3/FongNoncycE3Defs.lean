module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGNonDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs onLie)

@[expose] def KGNoncycCentE3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p → IsSimpleGroup K →
    (∃ x y : K, x * y ≠ y * x) → IsChevSimple 2 K → CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 →
    ∀ S B : Subgroup (MulAut K), IsPGroup 2 ↥S → ¬ IsCyclic ↥S →
      S ⊓ (MulAut.conj : K →* MulAut K).range = ⊥ → IsPGroup p ↥B →
      B ≤ normalizer (S : Set (MulAut K)) →
      ∃ σ₁ σ₂ : MulAut K, σ₁ ∈ S ∧ σ₂ ∈ S ∧ σ₁ ≠ 1 ∧ σ₂ ≠ 1 ∧
        (∀ τ ∈ S, τ * σ₁ = σ₁ * τ) ∧ (∀ τ ∈ S, τ * σ₂ = σ₂ * τ) ∧
        (∀ τ ∈ B, τ * σ₁ = σ₁ * τ) ∧ (∀ τ ∈ B, τ * σ₂ = σ₂ * τ) ∧
        Subgroup.closure ({k : K | σ₁ k = k} ∪ {k : K | σ₂ k = k}) = ⊤

@[expose] def KGThreeRankBig : TauCeti.LieTypeIndex → Prop
  | .A n q => 4 ≤ n ∧ q.p = 2 ∧ Even q.exponent
  | .D _ q => q.p = 2
  | .twistedD n q => 5 ≤ n ∧ q.p = 2
  | .F4 _ => True
  | .E6 _ => True
  | .E7 _ => True
  | .E8 _ => True
  | .twistedE6 _ => True
  | _ => False

@[expose] def KGNoncycCentSmall : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p → IsSimpleGroup K →
    (∃ x y : K, x * y ≠ y * x) → IsChevSimple 2 K → CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 →
    ¬ catalogIs K (onLie KGThreeRankBig) →
    ∀ S B : Subgroup (MulAut K), IsPGroup 2 ↥S → ¬ IsCyclic ↥S →
      S ⊓ (MulAut.conj : K →* MulAut K).range = ⊥ → IsPGroup p ↥B →
      B ≤ normalizer (S : Set (MulAut K)) →
      ∃ σ₁ σ₂ : MulAut K, σ₁ ∈ S ∧ σ₂ ∈ S ∧ σ₁ ≠ 1 ∧ σ₂ ≠ 1 ∧
        (∀ τ ∈ S, τ * σ₁ = σ₁ * τ) ∧ (∀ τ ∈ S, τ * σ₂ = σ₂ * τ) ∧
        (∀ τ ∈ B, τ * σ₁ = σ₁ * τ) ∧ (∀ τ ∈ B, τ * σ₂ = σ₂ * τ) ∧
        Subgroup.closure ({k : K | σ₁ k = k} ∪ {k : K | σ₂ k = k}) = ⊤

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
