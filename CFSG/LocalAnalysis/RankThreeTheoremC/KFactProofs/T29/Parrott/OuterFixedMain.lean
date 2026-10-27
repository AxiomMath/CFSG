module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedUnitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedSymplectic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedOrth
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedG2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedTriality
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedReeF4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open TauCeti

section Main


theorem outerFixedAt_of_rank (d : ValidLieTypeIndex) (hch : d.1.characteristic ≠ 3)
    (hd : IsRankTwoIndex d.1 ∨ IsRankThreeIndex d.1) : OuterFixedAt d := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_A] using hch
    have hq := card_mod_three_ne_zero hp3
    have hq2 : 2 ≤ q.card := q.isPrimePow_card.two_le
    simp only [IsRankTwoIndex, IsRankThreeIndex] at hd
    refine outerFixedAt_A r q hv (by omega) fun h => ?_
    have h1 := h.trans (Nat.gcd_dvd_left _ _)
    have h2 := h.trans (Nat.gcd_dvd_right _ _)
    omega
  | twistedA r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_twistedA] using hch
    have hq := card_mod_three_ne_zero hp3
    simp only [IsRankTwoIndex, IsRankThreeIndex] at hd
    refine outerFixedAt_twistedA r q hv (by omega) hp3 fun h => ?_
    have h1 := h.trans (Nat.gcd_dvd_left _ _)
    have h2 := h.trans (Nat.gcd_dvd_right _ _)
    omega
  | B r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_B] using hch
    simp only [IsRankTwoIndex, IsRankThreeIndex] at hd
    rcases hd with rfl | rfl
    · exact outerFixedAt_B2 q hv
    · by_cases hp2 : q.p = 2
      · exact outerFixedAt_B3_even q hv hp2
      · exact outerFixedAt_B3_odd q hv hp2 hp3
  | C r q =>
    simp only [IsRankTwoIndex, IsRankThreeIndex, false_or] at hd
    subst hd
    exact outerFixedAt_C3 q hv
  | twistedD r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_twistedD] using hch
    simp only [IsRankTwoIndex, IsRankThreeIndex, false_or] at hd
    subst hd
    exact outerFixedAt_twistedD4 q hv hp3
  | G2 q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_G2] using hch
    exact outerFixedAt_G2 q hv hp3
  | trialityD4 q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_trialityD4] using hch
    exact outerFixedAt_trialityD4 q hv hp3
  | reeF4 m => exact outerFixedAt_reeF4 m hv
  | D r q => exact (hd.elim id id).elim
  | E6 q => exact (hd.elim id id).elim
  | E7 q => exact (hd.elim id id).elim
  | E8 q => exact (hd.elim id id).elim
  | F4 q => exact (hd.elim id id).elim
  | twistedE6 q => exact (hd.elim id id).elim
  | suzuki k => exact (hd.elim id id).elim
  | reeG2 k => exact (hd.elim id id).elim
  | tits => exact (hd.elim id id).elim

theorem outerFixedE9_holds : OuterFixedE9 :=
  outerFixedE9_of_forall outerFixedAt_of_rank

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
