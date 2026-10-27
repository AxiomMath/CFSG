module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I811CycDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsDvd
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankExcTwoA
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankExcTwoB
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankExcTwoC
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankExcTwoD
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankSporadic

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.CoprimeTwo

open CFSG.Open TauCeti CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank
  CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls

set_option linter.unusedSectionVars false


theorem kFactCoprimeThreeTwoPart
    : KFactCoprimeThreeTwoPart := by
  intro S _ _ _ hnab ⟨i, ⟨e⟩⟩ h3
  have : Nontrivial S := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  cases i with
  | cyclic p hp =>
    obtain ⟨a, b, hab⟩ := hnab
    refine (hab (e.injective ?_)).elim
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    refine (h3 ?_).elim
    rw [Nat.card_congr e.toEquiv]
    have hn2 : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    have hc : Nat.card (alternatingGroup (Fin n)) = (Nat.factorial n) / 2 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    rw [hc]
    have h3f : 3 ∣ Nat.factorial n := Nat.dvd_factorial (by norm_num) (by omega)
    have h2f : 2 ∣ Nat.factorial n := Nat.dvd_factorial (by norm_num) (by omega)
    obtain ⟨k, hk⟩ := h2f
    have : (Nat.factorial n) / 2 = k := by omega
    rw [this]
    rw [hk] at h3f
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 2) h3f)
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | A r q => exact (h3 (A_three_dvd_card hv e)).elim
    | twistedA r q => exact (h3 (twistedA_three_dvd_card hv e)).elim
    | B r q => exact (h3 (three_dvd_card_of_two_le_pRank (B_two_le_pRank_three hv e))).elim
    | C r q => exact (h3 (three_dvd_card_of_two_le_pRank (C_two_le_pRank_three hv e))).elim
    | D r q => exact (h3 (three_dvd_card_of_two_le_pRank (D_two_le_pRank_three hv e))).elim
    | twistedD r q =>
      exact (h3 (three_dvd_card_of_two_le_pRank (twistedD_two_le_pRank_three hv e))).elim
    | E6 q => exact (h3 (three_dvd_card_of_two_le_pRank (two_le_pRank_three_exc_e6 q hv e))).elim
    | E7 q => exact (h3 (three_dvd_card_of_two_le_pRank (two_le_pRank_three_exc_e7 q hv e))).elim
    | E8 q => exact (h3 (three_dvd_card_of_two_le_pRank (two_le_pRank_three_exc_e8 q hv e))).elim
    | F4 q => exact (h3 (three_dvd_card_of_two_le_pRank (two_le_pRank_three_exc_f4 q hv e))).elim
    | G2 q => exact (h3 (three_dvd_card_of_two_le_pRank (two_le_pRank_three_exc_g2 q hv e))).elim
    | twistedE6 q =>
      exact (h3 (three_dvd_card_of_two_le_pRank (two_le_pRank_three_exc_twistedE6 q hv e))).elim
    | trialityD4 q =>
      exact (h3 (three_dvd_card_of_two_le_pRank (two_le_pRank_three_exc_trialityD4 q hv e))).elim
    | reeG2 m =>
      exact (h3 (three_dvd_card_of_two_le_pRank (two_le_pRank_three_exc_reeG2 m hv e))).elim
    | reeF4 m =>
      exact (h3 (three_dvd_card_of_two_le_pRank (two_le_pRank_three_exc_reeF4 m hv e))).elim
    | tits => exact (h3 (three_dvd_card_of_two_le_pRank (two_le_pRank_three_exc_tits hv e))).elim
    | suzuki m =>
      obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e'⟩⟩ := suzukiModel_cat hv
      have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
      rw [Nat.card_congr e.toEquiv, Nat.card_congr e'.toEquiv,
        CFSG.LieType.Ree.suzuki_order hF']
      have h1 : 1 ≤ a := by omega
      have : 64 ∣ (2 ^ (2 * a + 1)) ^ 2 := by
        rw [← pow_mul]
        have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
        rw [h64]
        exact pow_dvd_pow 2 (by omega : 6 ≤ (2 * a + 1) * 2)
      exact (this.mul_right _).mul_right _
  | sporadic s =>
    by_cases hs : s = .J1
    · subst hs
      refine (h3 ?_).elim
      obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group .J1
      rw [Nat.card_congr (e.trans b.symm).toEquiv]
      change 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J1
      rw [CFSG.Sporadic.J1.card_J1]
      norm_num
    · exact (h3 (three_dvd_card_of_two_le_pRank
        (ThreeRankSpor.two_le_pRank_three_sporadic_ne_J1 hs ⟨e⟩))).elim

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.CoprimeTwo
