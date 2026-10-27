module

public import CFSG.LocalAnalysis.Mason73.FinalIdentification
public import CFSG.LocalAnalysis.Mason73.L4SylowComparisonCongruence
public import CFSG.LocalAnalysis.Mason73.L4ExclExceptionalE32
public import CFSG.LocalAnalysis.Mason73.L4ExclZModFour
public import CFSG.LocalAnalysis.Mason73.L4ExclRank
public import CFSG.LocalAnalysis.Mason73.L4ExclInvertedBlock
public import CFSG.LocalAnalysis.Mason73.L4ExclOrderSix
public import CFSG.LocalAnalysis.Mason73.L4ExclSymplectic
public import CFSG.LocalAnalysis.Mason73.L4ExclRee

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow


theorem l4SylowComparison : L4SylowComparison := by
  intro G _ _ _ n hn P hP hOdd
  obtain ⟨t, r, p, f, hp, hp2, hadm, hL⟩ := hOdd
  have hf : 1 ≤ f := hadm.2.1
  have hq4 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 :=
    Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp (hp.eq_two_or_odd'.resolve_left hp2).pow)
  cases t with
  | PSL =>
    have hr : 2 ≤ r := hadm.2.2.1
    rcases (show r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ 7 ≤ r by omega) with
      rfl | rfl | rfl | rfl | rfl | hr7
    · exact (false_of_lieModel_psl_two_of_l4Sylow hn P hP hp hp2 hL).elim
    · exact (false_of_lieModel_psl_three_of_l4Sylow hn P hP hp2 hL).elim
    · rcases hq4 with hq | hq
      · exact litPSLU4S_of_lieModel_psl4_l4Sylow hp (by omega) hq hL hn P hP
      · exact (false_of_lieModel_psl_four_of_l4Sylow hn P hP hp hp2 hL hq).elim
    · rcases hq4 with hq | hq
      · exact (false_of_lieModel_psl_five_of_l4Sylow hn P hP hp hp2 hL hq).elim
      · exact (false_of_lieModel_psl_five_of_l4Sylow_of_mod_four_three hn P hP hL hq).elim
    · rcases hq4 with hq | hq
      · exact (false_of_lieModel_psl_of_l4Sylow hn P hP hp hp2 hL (Or.inr ⟨rfl, hq⟩)).elim
      · exact (false_of_lieModel_psl_six_of_l4Sylow hn P hP hL hq).elim
    · exact (false_of_lieModel_psl_of_l4Sylow hn P hP hp hp2 hL (Or.inl hr7)).elim
  | PSU =>
    have hr : 3 ≤ r := hadm.2.2.1
    rcases (show r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ 7 ≤ r by omega) with
      rfl | rfl | rfl | rfl | hr7
    · exact (false_of_lieModel_psu_three_of_l4Sylow hn P hP hp2 hL).elim
    · rcases hq4 with hq | hq
      · exact (false_of_lieModel_psu_four_of_l4Sylow hn P hP hp2 hL hq).elim
      · exact litPSLU4S_of_lieModel_psu4_l4Sylow hp (by omega) hq hL hn P hP
    · rcases hq4 with hq | hq
      · exact (false_of_lieModel_psu_five_of_l4Sylow_of_mod_four_one hn P hP hL hq).elim
      · exact (false_of_lieModel_psu_five_of_l4Sylow hn P hP hp hp2 hL hq).elim
    · rcases hq4 with hq | hq
      · exact (false_of_lieModel_psu_six_of_l4Sylow hn P hP hL hq).elim
      · exact (false_of_lieModel_psu_of_l4Sylow hn P hP hp hp2 hL (Or.inr ⟨rfl, hq⟩)).elim
    · exact (false_of_lieModel_psu_of_l4Sylow hn P hP hp hp2 hL (Or.inl hr7)).elim
  | PSp =>
    have hr : 2 ≤ r := hadm.2.2.1
    rcases (show r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with rfl | rfl | hr4
    · exact (false_of_lieModel_psp_two_of_l4Sylow hn P hP hp hp2 hL).elim
    · exact (false_of_lieModel_psp_three_of_l4Sylow hn P hP hp hp2 hL).elim
    · exact (false_of_lieModel_psp_of_l4Sylow hn P hP hp hL hr4).elim
  | POmegaOdd =>
    exact (false_of_lieModel_pOmegaOdd_of_l4Sylow hn P hP hp hp2 hL hadm.2.2.1).elim
  | POmegaPlus =>
    exact (false_of_lieModel_pOmegaPlus_of_l4Sylow hn P hP hp hp2 hL hadm.2.2).elim
  | POmegaMinus =>
    exact (false_of_lieModel_pOmegaMinus_of_l4Sylow hn P hP hp hp2 hL hadm.2.2).elim
  | G2 => exact (false_of_lieModel_g2_of_l4Sylow hn P hP hp hp2 hL).elim
  | F4 =>
    exact (false_of_lieModel_untwisted_E32_of_l4Sylow hn P hP hp hp2 (Or.inl rfl) hL).elim
  | E6 =>
    exact (false_of_lieModel_untwisted_E32_of_l4Sylow hn P hP hp hp2 (Or.inr (Or.inl rfl))
      hL).elim
  | E7 =>
    exact (false_of_lieModel_untwisted_E32_of_l4Sylow hn P hP hp hp2
      (Or.inr (Or.inr (Or.inl rfl))) hL).elim
  | E8 =>
    exact (false_of_lieModel_untwisted_E32_of_l4Sylow hn P hP hp hp2
      (Or.inr (Or.inr (Or.inr rfl))) hL).elim
  | twistedE6 => exact (false_of_lieModel_twistedE6_of_l4Sylow hn P hP hp hp2 hL).elim
  | trialityD4 => exact (false_of_lieModel_trialityD4_of_l4Sylow hn P hP hp hp2 hL).elim
  | twistedB2 => exact absurd hadm.2.2.2.1 hp2
  | twistedG2 => exact (false_of_lieModel_twistedG2_of_l4Sylow hn P hP hL).elim
  | twistedF4 => exact absurd hadm.2.2.2.1 hp2
  | Tits => exact absurd hadm.2.2.2.1 hp2

end CFSG.LocalAnalysis.Mason73
