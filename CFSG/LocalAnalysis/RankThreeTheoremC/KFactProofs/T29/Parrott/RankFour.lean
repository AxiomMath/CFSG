module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankFourLin
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Assembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankFourOrth

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open TauCeti

theorem rankFourOpen_holds : RankFourOpen := by
  intro d hch hd K _ _ ⟨e⟩
  obtain ⟨dd, hv⟩ := d
  have hr := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases dd with
  | A r q =>
    obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) f]
    have hFq : Nat.card F = q.card := hF.trans (PrimePower.card_def q).symm
    rcases hd with ⟨hr4, hq⟩ | ⟨hr7, -⟩
    · exact four_le_pRank_projSL_of_dvd (by omega) (by rw [hFq]; omega)
    · exact four_le_pRank_projSL_of_eight_le (by omega)
  | twistedA r q =>
    obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) f]
    have hqc : q.card = q.p ^ q.exponent := PrimePower.card_def q
    rcases hd with ⟨hr4, hq⟩ | ⟨hr7, hq⟩
    · exact four_le_pRank_projSU_of_dvd_add hF (by omega) (by rw [← hqc]; omega)
    · haveI : Fact q.p.Prime := ⟨q.prime_p⟩
      haveI : CharP F q.p :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
          (k := q.exponent * 2) (by have := q.exponent_pos; omega) (by rw [hF, ← pow_mul])
      exact four_le_pRank_projSU_of_dvd_sub hF (by omega) (by rw [← hqc]; exact hq)
  | B r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_B] using hch
    have hr4 : 4 ≤ r := hd
    by_cases hp2 : q.p = 2
    · obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp2 (by omega) e
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) f]
      exact four_le_pRank_projSp_of_four_le hr4
    · exact four_le_pRank_three_orth
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 (by omega) e)
        (Or.inl ⟨rfl, hr4⟩) hp3
  | C r q =>
    have hr4 : 4 ≤ r := hd
    obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) f]
    exact four_le_pRank_projSp_of_four_le hr4
  | D r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_D] using hch
    have hr4 : 4 ≤ r := hr
    exact four_le_pRank_three_orth
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e)
      (Or.inr (Or.inl ⟨rfl, hr4⟩)) hp3
  | twistedD r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_twistedD] using hch
    have hr5 : 5 ≤ r := hd
    exact four_le_pRank_three_orth
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e)
      (Or.inr (Or.inr ⟨rfl, hr5⟩)) hp3
  | E6 q => exact hd.elim
  | E7 q => exact hd.elim
  | E8 q => exact hd.elim
  | F4 q => exact hd.elim
  | G2 q => exact hd.elim
  | twistedE6 q => exact hd.elim
  | trialityD4 q => exact hd.elim
  | suzuki k => exact hd.elim
  | reeG2 k => exact hd.elim
  | reeF4 k => exact hd.elim
  | tits => exact hd.elim

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
