module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin

@[expose] def KFactSmallNoTwo : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → ¬ (p = 5 ∧ IsFi22 K) →
      ∀ S : Sylow p K, ∀ U : Subgroup K, IsPGroup 2 U →
        (S : Subgroup K) ≤ Subgroup.normalizer (U : Set K) → U = ⊥

@[expose] def KFactSmallSylowShape : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
      Nat.card T = p ^ 2 ∨ (Nat.card T = p ^ 3 ∧ Nat.card (Subgroup.center T) = p)

@[expose] def KFactSmallOrbits : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → ¬ (p = 5 ∧ IsFi22 K) →
      Nat.card T = p ^ 2 →
      (∀ O : Set K, O ⊆ (T : Set K) \ {1} →
        (∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ t ∈ O, n * t * n⁻¹ ∈ O) →
        O.ncard = 0 ∨ O.ncard = p ^ 2 - 1) ∨
      (IsSmallLinTwo p K ∧ 5 ≤ p ∧ ∀ O : Set K, O ⊆ (T : Set K) \ {1} →
        (∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ t ∈ O, n * t * n⁻¹ ∈ O) →
        O.ncard = 0 ∨ O.ncard = p ^ 2 - 1 ∨ 2 * O.ncard = p ^ 2 - 1) ∨
      (IsAltTwoP p K ∧ ∀ O : Set K, O ⊆ (T : Set K) \ {1} →
        (∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ t ∈ O, n * t * n⁻¹ ∈ O) →
        O.ncard = 0 ∨ O.ncard = p ^ 2 - 1 ∨ O.ncard = 2 * (p - 1) ∨ O.ncard = (p - 1) ^ 2)

end CFSG.AGLEmbedding
