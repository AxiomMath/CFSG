module

public import CFSG.LocalAnalysis.AGLEmbedding.KGenTwoModAbFix

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def KFactAlphaConclusionW (K : Type) [Group K] [Finite K] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → Subgroup.center K ≠ ⊥ → IsPGroup p (Subgroup.center K) →
    IsCyclic (Subgroup.center K) → ∀ T : Sylow p K,
      (KGenThree p K ∧ (3 ≤ Open.pRank p (⊤ : Subgroup K) ∨ KOutNormalSylow p K)) ∨
      (KGenTwoModAbFix p K ∧ Nat.card (Subgroup.center K) = p ∧ KOutNormalSylow p K) ∨
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 ∨
      (GLBWeakCore p (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank p (⊤ : Subgroup K)) ∨
      (KOutTwoGroup K ∧
        ((∃ A : Subgroup K, A ≤ (T : Subgroup K) ⊓ Subgroup.centralizer (T : Set K) ∧
            IsElemAbelian p A ∧ Nat.card A = p ^ 2) ∨
          ((∀ t ∈ (T : Subgroup K), t ^ p = 1) ∧ Open.pRank p (T : Subgroup K) ≤ 3) ∨
          (∃ A : Subgroup K, A ≤ (T : Subgroup K) ∧
            (T : Subgroup K) ≤ Subgroup.normalizer (A : Set K) ∧ IsElemAbelian p A ∧
            p ^ (p + 1) ≤ Nat.card A)))

@[expose] def KFactAlphaW : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K →
    IsCatalogGroup (K ⧸ Subgroup.center K) → KFactAlphaConclusionW K

end CFSG.AGLEmbedding
