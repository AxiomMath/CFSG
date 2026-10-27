module

public import CFSG.LocalAnalysis.OddStandard.ThmCSylowOrder
public import CFSG.LocalAnalysis.OddStandard.ThmCSylowPermModels
public import CFSG.LocalAnalysis.OddStandard.ThmCSylowSz
public import CFSG.LocalAnalysis.OddStandard.ThmCSylowSp4
public import CFSG.LocalAnalysis.OddStandard.ThmCSylowG2
public import CFSG.LocalAnalysis.OddStandard.ThmCSylowD4
public import CFSG.GH74.Orders.LieType
public import CFSG.GH74.Orders.Sporadic

public section

namespace CFSG.OddStandard.ThmC

open CFSG CFSG.Open CFSG.GH74 CFSG.Blueprint CFSG.OddStandard.ThmC.T
  CFSG.OddStandard.ThmC.Sylow CFSG.GH74.GLS.Bg.TwoGroups

theorem ne_two_of_pow_mod_four_eq_one {p f : ℕ} (hf : 1 ≤ f) (hq : p ^ f % 4 = 1) : p ≠ 2 := by
  rintro rfl
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rcases g with _ | g
  · simp at hq
  · rw [pow_succ, pow_succ] at hq
    omega

theorem sylowComparison :
    SylowComparison := by
  intro K _ _ _ hK T hT
  have hT' : IsT (T : Subgroup K) := hT
  rcases hK with ⟨p, f, hp, hp2, hf, hG2 | hD4⟩ | ⟨p, f, hp, hp2, hf, hPSp⟩ | ⟨f, hRee⟩ |
    ⟨p, f, hp, hp2, hf, -, hL4⟩ | ⟨p, f, hp, hp2, hf, -, hU4⟩ | ⟨p, f, hp, hf, hq, hL5⟩ |
    ⟨p, f, hp, hf, hq, hU5⟩ | (hL28 | hL216 | hL34 | hSz) | ⟨n, hn8, hn11, ⟨e⟩⟩ |
    (hM12 | hM22 | hM23 | hJ1 | hJ2 | hJ3 | hMcL | hLy)
  · exact (false_of_lieModel_g2 hp hp2 hG2 T hT').elim
  · exact (false_of_lieModel_d4 hp hp2 hD4 T hT').elim
  · exact (false_of_lieModel_psp hp hp2 hPSp T hT').elim
  · obtain ⟨k, -, hcard⟩ := card_of_lieModel_twistedG2 hRee
    exact (false_of_not_two_pow_six_dvd T hT' (by
      rw [hcard]
      exact not_two_pow_six_dvd_ordRee k)).elim
  · have hcard := card_of_lieModel_PSL (by norm_num : 4 ≠ 0) hL4
    exact (false_of_two_pow_seven_dvd T hT' (by
      rw [hcard]
      exact two_pow_seven_dvd_ordA_three (hp.odd_of_ne_two hp2).pow)).elim
  · have hcard := card_of_lieModel_PSU (by norm_num : 4 ≠ 0) hp2 hU4
    exact (false_of_two_pow_seven_dvd T hT' (by
      rw [hcard]
      exact two_pow_seven_dvd_ordTwistedA_three (hp.odd_of_ne_two hp2).pow)).elim
  · have hcard := card_of_lieModel_PSL (by norm_num : 5 ≠ 0) hL5
    have hodd : Odd (p ^ f) := Nat.odd_iff.2 (by omega)
    exact (false_of_two_pow_seven_dvd T hT' (by
      rw [hcard]
      exact two_pow_seven_dvd_ordA_four hodd)).elim
  · have hp2 := ne_two_of_pow_mod_four_eq_one hf hq
    have hcard := card_of_lieModel_PSU (by norm_num : 5 ≠ 0) hp2 hU5
    exact (false_of_two_pow_seven_dvd T hT' (by
      rw [hcard]
      exact two_pow_seven_dvd_ordTwistedA_four (hp.odd_of_ne_two hp2).pow)).elim
  · have hcard := card_of_lieModel_PSL (by norm_num : 2 ≠ 0) hL28
    exact (false_of_not_two_pow_six_dvd T hT' (by
      rw [hcard]
      change ¬ 2 ^ 6 ∣ ordA 1 8
      rw [ordA_one_eight]
      decide)).elim
  · have hcard := card_of_lieModel_PSL (by norm_num : 2 ≠ 0) hL216
    exact (false_of_not_two_pow_six_dvd T hT' (by
      rw [hcard]
      change ¬ 2 ^ 6 ∣ ordA 1 16
      rw [ordA_one_sixteen]
      decide)).elim
  · exact hL34
  · exact (false_of_lieModel_sz8 hSz T hT').elim
  · exact (false_of_alternating (by omega) e T hT').elim
  · exact (false_of_sporadic_M12 hM12 T hT').elim
  · have hcard := card_of_isSporadic_M22 hM22
    exact (false_of_two_pow_seven_dvd T hT' (by rw [hcard]; norm_num)).elim
  · have hcard := card_of_isSporadic_M23 hM23
    exact (false_of_two_pow_seven_dvd T hT' (by rw [hcard]; norm_num)).elim
  · have hcard := card_of_isSporadic_J1 hJ1
    exact (false_of_not_two_pow_six_dvd T hT' (by rw [hcard]; norm_num)).elim
  · have hcard := card_of_isSporadic_J2 hJ2
    exact (false_of_two_pow_seven_dvd T hT' (by rw [hcard]; norm_num)).elim
  · have hcard := card_of_isSporadic_J3 hJ3
    exact (false_of_two_pow_seven_dvd T hT' (by rw [hcard]; norm_num)).elim
  · have hcard := card_of_isSporadic_McL hMcL
    exact (false_of_two_pow_seven_dvd T hT' (by rw [hcard]; norm_num)).elim
  · have hcard := card_of_isSporadic_Ly hLy
    exact (false_of_two_pow_seven_dvd T hT' (by rw [hcard]; norm_num)).elim

end CFSG.OddStandard.ThmC
