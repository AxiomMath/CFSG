module

public import CFSG.LocalAnalysis.AGLEmbedding.KGenTwoModAbFix
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def KFactCaseTwoAlphaElimW : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K →
    IsCatalogGroup (K ⧸ Subgroup.center K) → ∀ p : ℕ, (p = 3 ∨ p = 5) →
    Subgroup.center K ≠ ⊥ → IsPGroup p (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    ∀ (A : Subgroup K) (L : Type) [Group L], IsCaseTwoGroup p L →
      ∀ f : A →* L, Function.Surjective f → ∀ T : Sylow p K,
        (KGenThree p K ∧ (3 ≤ Open.pRank p (⊤ : Subgroup K) ∨ KOutNormalSylow p K)) ∨
        (KGenTwoModAbFix p K ∧ Nat.card (Subgroup.center K) = p ∧ KOutNormalSylow p K) ∨
        Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 ∨
        (GLBWeakCore p (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank p (⊤ : Subgroup K))

@[expose] def KFactCaseTwoAlphaElimThreeW : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K →
    IsCatalogGroup (K ⧸ Subgroup.center K) →
    Subgroup.center K ≠ ⊥ → IsPGroup 3 (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    ∀ (A : Subgroup K) (L : Type) [Group L], IsCaseTwoGroup 3 L →
      ∀ f : A →* L, Function.Surjective f → ∀ T : Sylow 3 K,
        (KGenThree 3 K ∧ (3 ≤ Open.pRank 3 (⊤ : Subgroup K) ∨ KOutNormalSylow 3 K)) ∨
        (KGenTwoModAbFix 3 K ∧ Nat.card (Subgroup.center K) = 3 ∧ KOutNormalSylow 3 K) ∨
        Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 ∨
        (GLBWeakCore 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank 3 (⊤ : Subgroup K))

theorem kFactCaseTwoAlphaElimW_of_three (h5 : KFactAlphaFive)
    (h3 : KFactCaseTwoAlphaElimThreeW) : KFactCaseTwoAlphaElimW := by
  intro K _ _ hK hcat p hp hZ hZp hZc A L _ hL f hf T
  rcases hp with rfl | rfl
  · exact h3 K hK hcat hZ hZp hZc A L hL f hf T
  · rcases h5 K hK hcat 5 Nat.prime_five le_rfl hZ hZp hZc T with ha | hb | ⟨hc, h3'⟩
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inl hb))
    · refine Or.inr (Or.inr (Or.inr ⟨eq_top_iff.mpr ?_, h3'⟩))
      rw [← hc]
      exact PreuniquenessRankFour.Helpers.rankThreeCore_le_weakCore 5 Nat.prime_five _

end CFSG.AGLEmbedding
