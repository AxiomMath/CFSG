module

public import CFSG.LocalAnalysis.SectionRank.QTK.List
public import CFSG.LocalAnalysis.SectionRank.QTK.Basic
import CFSG.LocalAnalysis.SectionRank.QTK.EvenMinus8
import CFSG.RankThree.PartOne.KF.ClsSpWit
import CFSG.RankThree.PartTwo.KFacts.KS21LocalRankOmega
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.SectionRank.QTK

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

theorem qtkSimpleList_of_psp_even {S : Type} [Group S] [Finite S] {n f : ℕ}
    (hQT : CFSG.Open.evenRank S ≤ 2) (hm : StatedClassicalModel S .PSp n 2 f) :
    QTKSimpleList S := by
  obtain ⟨⟨-, hf, hn, h22⟩, K, _, _, hK, ⟨e⟩⟩ := id hm
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | hn4
  · have hf2 : 2 ≤ f := by
      by_contra h
      exact h22 (by rw [show f = 1 by omega]; rfl)
    exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inl ⟨hf2, hm⟩)))⟩)))
  · by_cases hf1 : f = 1
    · subst hf1
      exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr hm))))
    · obtain ⟨r, hr, hr2, -, hrd⟩ :=
        CFSG.RankThree.PartTwo.Census.exists_prime_ne_five_dvd_two_pow_sub_one (f := f) (by omega)
      exact absurd hQT (not_evenRank_le_two_of_localRank e hr hr2
        (CFSG.RankThree.PartOne.KFU.le_localRank_statedSp_torus hr hr2
          (by rw [Nat.card_units, hK]; exact hrd) (by norm_num)))
  · refine absurd hQT (not_evenRank_le_two_of_localRank e Nat.prime_three (by norm_num) ?_)
    intro _
    rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
      (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _
        (CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedSp_eq_bot (K := K) (n := n)
          (by omega))) Nat.prime_three]
    exact (three_le_localRank_statedProj_statedOmegaPlus K hn4).trans
      (CFSG.RankThree.PartOne.KFU.localRank_statedProj_statedOmega_quadPlus_le (by omega)
        Nat.prime_three)

theorem not_evenRank_le_two_of_omegaPlus_even {S : Type} [Group S] [Finite S] {n f : ℕ}
    (hm : StatedClassicalModel S .POmegaPlus n 2 f) : ¬ CFSG.Open.evenRank S ≤ 2 := by
  obtain ⟨⟨-, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact not_evenRank_le_two_of_localRank e Nat.prime_three (by norm_num)
    (three_le_localRank_statedProj_statedOmegaPlus K hn)

theorem not_evenRank_le_two_of_omegaMinus_even {S : Type} [Group S] [Finite S] {n f : ℕ}
    (hm : StatedClassicalModel S .POmegaMinus n 2 f) : ¬ CFSG.Open.evenRank S ≤ 2 := by
  obtain ⟨⟨-, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hm
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn5
  · by_cases hf1 : f = 1
    · subst hf1
      exact not_evenRank_le_two_of_localRank e Nat.prime_three (by norm_num)
        (three_le_localRank_statedProj_statedOmegaMinus_four_two (by rw [hK, pow_one]) hirr)
    · obtain ⟨r, hr, hr2, -, hrd⟩ :=
        CFSG.RankThree.PartTwo.Census.exists_prime_ne_five_dvd_two_pow_sub_one (f := f) (by omega)
      exact not_evenRank_le_two_of_localRank e hr hr2
        (CFSG.RankThree.PartTwo.KFacts.KS21LocalRank.le_localRank_statedOmegaMinus_torus hr hr2
          (by rw [Nat.card_units, hK]; exact hrd) b c)
  · exact not_evenRank_le_two_of_localRank e Nat.prime_three (by norm_num)
      (three_le_localRank_statedProj_statedOmegaMinus K hn5 b c)

end CFSG.SectionRank.QTK
