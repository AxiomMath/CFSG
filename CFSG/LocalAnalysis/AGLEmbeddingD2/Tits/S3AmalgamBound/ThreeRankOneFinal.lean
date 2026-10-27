module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactThreeRankOne
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsIndex
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankExcFinal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankSporadic

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls

open CFSG.Open TauCeti CFSG.LieType.SeitzGeneration
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank

set_option linter.unusedSectionVars false


theorem kFactThreeRankOneSimple
    :
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactThreeRankOneSimple := by
  intro S _ _ _ hnab i ⟨e⟩ h1
  have : Nontrivial S := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have hlt : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) → False := by
    intro h
    omega
  cases i with
  | cyclic p hp =>
    obtain ⟨a, b, hab⟩ := hnab
    refine (hab (e.injective ?_)).elim
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    by_cases h5 : n = 5
    · subst h5
      exact Or.inr (Or.inr ⟨e⟩)
    · have h6 : 6 ≤ n := by omega
      exact (hlt (two_le_pRank_of_equiv e
        (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.two_le_pRank_three_alternating h6))).elim
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | A r q =>
      by_cases hA1 : r = 1 ∧ q.p ≠ 3
      · obtain ⟨rfl, hp⟩ := hA1
        exact Or.inl ⟨⟨.A 1 q, hv⟩, Or.inl ⟨q, hp, rfl⟩, ⟨e⟩⟩
      by_cases hA2 : r = 2 ∧ q.card % 3 = 2
      · obtain ⟨rfl, hc⟩ := hA2
        exact Or.inl ⟨⟨.A 2 q, hv⟩, Or.inr (Or.inl ⟨q, hc, rfl⟩), ⟨e⟩⟩
      exact (hlt (A_two_le_pRank_three hv e hA1 hA2)).elim
    | twistedA r q =>
      by_cases hA : r = 2 ∧ q.card % 3 = 1
      · obtain ⟨rfl, hc⟩ := hA
        exact Or.inl ⟨⟨.twistedA 2 q, hv⟩, Or.inr (Or.inr ⟨q, hc, rfl⟩), ⟨e⟩⟩
      exact (hlt (twistedA_two_le_pRank_three hv e hA)).elim
    | B r q => exact (hlt (B_two_le_pRank_three hv e)).elim
    | C r q => exact (hlt (C_two_le_pRank_three hv e)).elim
    | D r q => exact (hlt (D_two_le_pRank_three hv e)).elim
    | twistedD r q => exact (hlt (twistedD_two_le_pRank_three hv e)).elim
    | E6 q => exact (pRank_three_ne_one_of_exceptional ⟨.E6 q, hv⟩ (by simp) ⟨e⟩ h1).elim
    | E7 q => exact (pRank_three_ne_one_of_exceptional ⟨.E7 q, hv⟩ (by simp) ⟨e⟩ h1).elim
    | E8 q => exact (pRank_three_ne_one_of_exceptional ⟨.E8 q, hv⟩ (by simp) ⟨e⟩ h1).elim
    | F4 q => exact (pRank_three_ne_one_of_exceptional ⟨.F4 q, hv⟩ (by simp) ⟨e⟩ h1).elim
    | G2 q => exact (pRank_three_ne_one_of_exceptional ⟨.G2 q, hv⟩ (by simp) ⟨e⟩ h1).elim
    | twistedE6 q =>
      exact (pRank_three_ne_one_of_exceptional ⟨.twistedE6 q, hv⟩ (by simp) ⟨e⟩ h1).elim
    | trialityD4 q =>
      exact (pRank_three_ne_one_of_exceptional ⟨.trialityD4 q, hv⟩ (by simp) ⟨e⟩ h1).elim
    | suzuki m =>
      exact (pRank_three_ne_one_of_exceptional ⟨.suzuki m, hv⟩ (by simp) ⟨e⟩ h1).elim
    | reeG2 m => exact (pRank_three_ne_one_of_exceptional ⟨.reeG2 m, hv⟩ (by simp) ⟨e⟩ h1).elim
    | reeF4 m => exact (pRank_three_ne_one_of_exceptional ⟨.reeF4 m, hv⟩ (by simp) ⟨e⟩ h1).elim
    | tits => exact (pRank_three_ne_one_of_exceptional ⟨.tits, hv⟩ (by simp) ⟨e⟩ h1).elim
  | sporadic s =>
    by_cases hs : s = .J1
    · subst hs
      exact Or.inr (Or.inl ⟨e⟩)
    · exact (hlt (CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankSpor.two_le_pRank_three_sporadic_ne_J1
        hs ⟨e⟩)).elim

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls
