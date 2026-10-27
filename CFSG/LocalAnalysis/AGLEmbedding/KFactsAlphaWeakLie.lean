module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeak
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem kFactAlphaConclusionW_of {K : Type} [Group K] [Finite K] (h : KFactAlphaConclusion K) :
    KFactAlphaConclusionW K := by
  intro p hp hp2 hZ hZp hZc T
  rcases h p hp hp2 hZ hZp hZc T with ha | hb | ⟨hc, h3⟩ | hd
  · exact Or.inl ha
  · exact Or.inr (Or.inr (Or.inl hb))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨eq_top_iff.mpr ?_, h3⟩)))
    rw [← hc]
    exact PreuniquenessRankFour.Helpers.rankThreeCore_le_weakCore p hp _
  · exact Or.inr (Or.inr (Or.inr (Or.inr hd)))

@[expose] def KFactAlphaLieW : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) → KFactAlphaConclusionW K

theorem kFactAlphaW_of_families (halt : KFactAlphaAlt) (hlie : KFactAlphaLieW)
    (hspor : KFactAlphaSpor) : KFactAlphaW := by
  intro K _ _ hK hcat
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic p hp =>
    exact (not_nonempty_mulEquiv_zmod
      (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK) ⟨e⟩).elim
  | alternating n hn => exact kFactAlphaConclusionW_of (halt K hK n hn ⟨e⟩)
  | lie d => exact hlie K hK d ⟨e⟩
  | sporadic s => exact kFactAlphaConclusionW_of (hspor K hK s ⟨e⟩)

@[expose] def KFactAlphaLieThreeW : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    Subgroup.center K ≠ ⊥ → IsPGroup 3 (Subgroup.center K) →
    IsCyclic (Subgroup.center K) → ∀ T : Sylow 3 K,
      (KGenThree 3 K ∧ (3 ≤ Open.pRank 3 (⊤ : Subgroup K) ∨ KOutNormalSylow 3 K)) ∨
      (KGenTwoModAbFix 3 K ∧ Nat.card (Subgroup.center K) = 3 ∧ KOutNormalSylow 3 K) ∨
      Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 ∨
      (GLBWeakCore 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank 3 (⊤ : Subgroup K)) ∨
      (KOutTwoGroup K ∧
        ((∃ A : Subgroup K, A ≤ (T : Subgroup K) ⊓ Subgroup.centralizer (T : Set K) ∧
            IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2) ∨
          ((∀ t ∈ (T : Subgroup K), t ^ 3 = 1) ∧ Open.pRank 3 (T : Subgroup K) ≤ 3) ∨
          (∃ A : Subgroup K, A ≤ (T : Subgroup K) ∧
            (T : Subgroup K) ≤ Subgroup.normalizer (A : Set K) ∧ IsElemAbelian 3 A ∧
            3 ^ (3 + 1) ≤ Nat.card A)))

theorem kFactAlphaLieW_of_three (h5 : KFactAlphaFive) (h3 : KFactAlphaLieThreeW) :
    KFactAlphaLieW := by
  intro K _ _ hK d he p hp hp2 hZ hZp hZc T
  by_cases h3p : p = 3
  · subst h3p
    exact h3 K hK d he hZ hZp hZc T
  rcases h5 K hK ⟨_, he⟩ p hp (hp.five_le_of_ne_two_of_ne_three hp2 h3p) hZ hZp hZc T with
    ha | hb | ⟨hc, h3'⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inr (Or.inl hb))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨eq_top_iff.mpr ?_, h3'⟩)))
    rw [← hc]
    exact PreuniquenessRankFour.Helpers.rankThreeCore_le_weakCore p hp _

end CFSG.AGLEmbedding
