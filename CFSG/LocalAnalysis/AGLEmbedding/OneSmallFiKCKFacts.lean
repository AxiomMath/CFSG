module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin

@[expose] def KFactFi22NoTwo : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsFi22 K → ∀ S : Sylow 5 K, ∀ U : Subgroup K,
    IsPGroup 2 U → (S : Subgroup K) ≤ Subgroup.normalizer (U : Set K) → U = ⊥

@[expose] def KFactFi22Orbits : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsFi22 K → ∀ T : Sylow 5 K, ∀ O : Set K,
    O ⊆ ((T : Subgroup K) : Set K) \ {1} →
    (∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ t ∈ O, n * t * n⁻¹ ∈ O) →
    O.ncard = 0 ∨ O.ncard = 5 ^ 2 - 1

theorem kFactSmallNoTwo_all (hNo2 : KFactSmallNoTwo) (hF : KFactFi22NoTwo)
    (K : Type) [Group K] [Finite K] (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a)
    (hc : IsCatalogGroup K) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (T : Sylow p K)
    (hT : ¬ IsCyclic (T : Subgroup K)) (hΓ : GLBCore p 1 (T : Subgroup K) ≠ ⊤)
    (hsm : Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2) (S : Sylow p K) (U : Subgroup K)
    (hU : IsPGroup 2 U) (hSU : (S : Subgroup K) ≤ Subgroup.normalizer (U : Set K)) : U = ⊥ := by
  by_cases hFi : p = 5 ∧ IsFi22 K
  · obtain ⟨rfl, hK⟩ := hFi
    exact hF K hK S U hU hSU
  · exact hNo2 K hs hnab hc p hp hp2 T hT hΓ hsm hFi S U hU hSU

@[expose] def KFactSmallOfRankTwo : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      Open.pRank p (⊤ : Subgroup K) ≤ 2 → Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2

theorem kFactSmallOfRankTwo_of (hAR : KFactSmallAutRank) : KFactSmallOfRankTwo := by
  intro K _ _ hs hnab hc p hp hp2 T hT hΓ hrk
  have : Fact p.Prime := ⟨hp⟩
  exact hAR K hs hnab hc p hp hp2 T hT hΓ ((CFSG.SectionRank.pRank_sylow T).1.trans_le hrk)

@[expose] def KFactSmallInvolveCard : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
    ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) →
      IsCatalogGroup L → ∀ TL : Sylow p L, ¬ IsCyclic (TL : Subgroup L) →
      GLBCore p 1 (TL : Subgroup L) ≠ ⊤ → Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ 2 →
    ∀ (A : Subgroup K) (f : A →* L), Function.Surjective f → Nat.card TL = Nat.card T

@[expose] def KFactCoverRankFive : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K →
    IsCatalogGroup (K ⧸ Subgroup.center K) → ∀ p : ℕ, p.Prime → 5 ≤ p →
    Subgroup.center K ≠ ⊥ → IsPGroup p (Subgroup.center K) → 4 ≤ Open.pRank p (⊤ : Subgroup K)

end CFSG.AGLEmbedding
