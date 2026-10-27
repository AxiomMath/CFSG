module

public import CFSG.LieType.Chevalley.GraphFixedData
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section


@[expose] def TwE6CrossRankStep : Prop :=
  ∀ {ℓ d p : ℕ}, ℓ.Prime → 1 ≤ d → p.Prime → 5 ≤ p → ℓ ≠ p →
    ∀ (K k : Type) [Field K] [Finite K] [Field k] [Finite k] (σ : K ≃+* K) (σ₀ : k ≃+* k),
      Nat.card K = (ℓ ^ (p * d)) ^ 2 → Nat.card k = (ℓ ^ d) ^ 2 →
      (∀ c, σ c = c ^ ℓ ^ (p * d)) → (∀ c, σ₀ c = c ^ ℓ ^ d) →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (graphFixedRootGroup TwistTag.E6 k σ₀.toRingHom))

@[expose] def TriD4CrossRankStep : Prop :=
  ∀ {ℓ d p : ℕ}, ℓ.Prime → 1 ≤ d → p.Prime → 5 ≤ p → ℓ ≠ p →
    ∀ (K k : Type) [Field K] [Finite K] [Field k] [Finite k] (σ : K ≃+* K) (σ₀ : k ≃+* k),
      Nat.card K = (ℓ ^ (p * d)) ^ 3 → Nat.card k = (ℓ ^ d) ^ 3 →
      (∀ c, σ c = c ^ ℓ ^ (p * d)) →
      ((∀ c, σ₀ c = c ^ ℓ ^ d) ∨ (∀ c, σ₀ c = c ^ (ℓ ^ d) ^ 2)) →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 k σ₀.toRingHom))

@[expose] def TriPhi1Rank : Prop :=
  ∀ {ℓ f : ℕ} [Fact ℓ.Prime], 1 ≤ f → ∀ {K : Type} [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ ℓ ^ f) →
    ∀ {p : ℕ}, p.Prime → 5 ≤ p → (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) - 1 →
      2 ≤ CFSG.pRank p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
