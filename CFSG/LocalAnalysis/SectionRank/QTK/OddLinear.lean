module

public import CFSG.LocalAnalysis.SectionRank.QTK.List
public import CFSG.LocalAnalysis.SectionRank.QTK.OddBasic
public import CFSG.LocalAnalysis.SectionRank.QTK.OddTorusU
import CFSG.RankThree.PartOne.Census3.LinearWitness
import CFSG.RankThree.PartTwo.Census.OddClassical.LinearWitness
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness
import CFSG.RankThree.PartTwo.Census.OddClassical.SymplecticWitness
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.SectionRank.QTK

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem not_dvd_four_of_odd_prime {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : ¬ r ∣ 4 := fun h4 =>
  hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
    (hr.dvd_of_dvd_pow (show r ∣ 2 ^ 2 by simpa using h4)))

theorem qtkSimpleList_of_psl_odd {S : Type} [Group S] [Finite S] {n p f : ℕ} (hp2 : p ≠ 2)
    (hQT : CFSG.Open.evenRank S ≤ 2) (hm : StatedClassicalModel S .PSL n p f) :
    QTKSimpleList S := by
  obtain ⟨⟨hp, hf, hn, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := id hm
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have h2 : (2 : K) ≠ 0 := CFSG.RankThree.PartOne.Census3.two_ne_zero_of_charP hp2
  set e' : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm
  rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | rfl | hn5
  · exact Or.inr (Or.inl ⟨p, hp, hp2, Or.inl ⟨f, hf, hm⟩⟩)
  · by_cases hf2 : f ≤ 2
    · exact Or.inr (Or.inl ⟨p, hp, hp2, Or.inr (Or.inl ⟨f, by omega, Or.inl hm⟩)⟩)
    · exact absurd hQT (not_evenRank_le_two_of_localRank e' hp hp2
        (le_trans (by omega) (CFSG.RankThree.PartOne.Census3.le_localRank_PSL_three hp2 hK)))
  · by_cases hf1 : f = 1
    · subst hf1
      by_cases hF : ∃ a : ℕ, p = 2 ^ a + 1
      · exact Or.inr (Or.inl ⟨p, hp, hp2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hF, hm⟩))))⟩)
      · obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_pred hp hp2 hF
        refine absurd hQT (not_evenRank_le_two_of_localRank e' hr hr2 ?_)
        refine le_localRank_PSL_torus_odd h2 (m := 3) hr ?_ (by norm_num) (by norm_num)
          (Or.inr (not_dvd_four_of_odd_prime hr hr2))
        rw [Nat.card_units, hK, pow_one]
        exact hrd
    · exact absurd hQT (not_evenRank_le_two_of_localRank e' hp hp2
        (le_trans (by omega) (CFSG.RankThree.PartOne.Census3.le_localRank_PSL_four hp2 hK)))
  · exact absurd hQT (not_evenRank_le_two_of_localRank e' hp hp2
      (le_trans (by omega) (CFSG.RankThree.PartTwo.Census.four_mul_le_localRank_PSL hp2 hK hn5)))

theorem qtkSimpleList_of_psu_odd {S : Type} [Group S] [Finite S] {n p f : ℕ} (hp2 : p ≠ 2)
    (hQT : CFSG.Open.evenRank S ≤ 2) (hm : StatedClassicalModel S .PSU n p f) :
    QTKSimpleList S := by
  obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := id hm
  have hU : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Finite K := hU.finite
  set e' : S ≃* unitaryPSU hU n := e.trans (unitaryPSUEquiv hU (by omega)).symm
  rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | hn5
  · by_cases hf2 : f ≤ 2
    · exact Or.inr (Or.inl ⟨p, hp, hp2, Or.inr (Or.inl ⟨f, by omega, Or.inr hm⟩)⟩)
    · exact absurd hQT (not_evenRank_le_two_of_localRank e' hp hp2 (le_trans (by simp; omega)
        (CFSG.RankThree.PartTwo.Census.le_localRank_unitaryPSU hU hp2 (r := 1) le_rfl
          (by norm_num))))
  · by_cases hf1 : f = 1
    · subst hf1
      by_cases hM : ∃ b : ℕ, p + 1 = 2 ^ b
      · exact Or.inr (Or.inl ⟨p, hp, hp2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hM, hm⟩))))⟩)
      · obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_succ hM
        exact absurd hQT (not_evenRank_le_two_of_localRank e hr hr2
          (le_localRank_statedSU_torus_odd hU hp2 (m := 3) hr (by rwa [pow_one]) (by norm_num)
            (by norm_num) (Or.inr (not_dvd_four_of_odd_prime hr hr2))))
    · exact absurd hQT (not_evenRank_le_two_of_localRank e' hp hp2
        (le_trans (by omega) (CFSG.RankThree.PartTwo.Census.le_localRank_unitaryPSU_four hU hp2)))
  · exact absurd hQT (not_evenRank_le_two_of_localRank e' hp hp2 (le_trans (by omega)
      (CFSG.RankThree.PartTwo.Census.le_localRank_unitaryPSU hU hp2 (r := 2) (by norm_num)
        (by omega))))

theorem qtkSimpleList_of_psp_odd {S : Type} [Group S] [Finite S] {n p f : ℕ} (hp2 : p ≠ 2)
    (hQT : CFSG.Open.evenRank S ≤ 2) (hm : StatedClassicalModel S .PSp n p f) :
    QTKSimpleList S := by
  obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := id hm
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
  · by_cases hf1 : f = 1
    · subst hf1
      exact Or.inr (Or.inl ⟨p, hp, hp2, Or.inr (Or.inr (Or.inl hm))⟩)
    · exact absurd hQT (not_evenRank_le_two_of_localRank e hp hp2
        (le_trans (by omega) (CFSG.RankThree.PartTwo.Census.le_localRank_PSp_two hp2 hK)))
  · exact absurd hQT (not_evenRank_le_two_of_localRank e hp hp2
      (le_trans (by norm_num) (CFSG.RankThree.PartTwo.Census.four_le_localRank_PSp hp2 hK hf hn3)))

end CFSG.SectionRank.QTK
