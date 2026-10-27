module

public import CFSG.LocalAnalysis.SectionRank.QTK.List
public import CFSG.LocalAnalysis.SectionRank.QTK.Basic
import CFSG.LocalAnalysis.SectionRank.QTK.EvenBlocks3
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.SectionRank.QTK

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

theorem three_dvd_two_pow_add_one {f : ℕ} (hf : Odd f) : 3 ∣ 2 ^ f + 1 := by
  obtain ⟨k, rfl⟩ := hf
  have h4 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [Nat.dvd_iff_mod_eq_zero, pow_succ, pow_mul]
  norm_num
  omega

theorem exists_prime_ne_five_dvd_two_pow_add_one {f : ℕ} (hf : 1 ≤ f) (hf2 : f ≠ 2) :
    ∃ r, r.Prime ∧ r ≠ 2 ∧ r ≠ 5 ∧ r ∣ 2 ^ f + 1 := by
  rcases Nat.even_or_odd f with ⟨k, hk⟩ | hodd
  · obtain ⟨r, hr, hr7, hrd⟩ :=
      CFSG.RankThree.PartTwo.Census.exists_prime_seven_le_dvd_two_pow_add_one (f := f) (by omega)
    exact ⟨r, hr, by omega, by omega, hrd⟩
  · exact ⟨3, Nat.prime_three, by norm_num, by norm_num, three_dvd_two_pow_add_one hodd⟩

theorem qtkSimpleList_of_psl_even {S : Type} [Group S] [Finite S] {n f : ℕ}
    (hQT : CFSG.Open.evenRank S ≤ 2) (hm : StatedClassicalModel S .PSL n 2 f) :
    QTKSimpleList S := by
  obtain ⟨⟨-, hf, hn, h22, -⟩, K, _, _, hK, ⟨e⟩⟩ := id hm
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  set e' : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm
  rcases (show n = 2 ∨ n = 3 ∨ (n = 4 ∨ n = 5) ∨ 6 ≤ n by omega) with rfl | rfl | h45 | hn6
  · have hf2 : 2 ≤ f := by
      by_contra h
      exact h22 (by rw [show f = 1 by omega]; rfl)
    exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inl ⟨hf2, hm⟩⟩)))
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inl ⟨hf, hm⟩)⟩)))
  · by_cases hf1 : f = 1
    · subst hf1
      exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨n, h45, hm⟩))))
    · obtain ⟨r, hr, hr2, -, hrd⟩ :=
        CFSG.RankThree.PartTwo.Census.exists_prime_ne_five_dvd_two_pow_sub_one (f := f) (by omega)
      refine absurd hQT (not_evenRank_le_two_of_localRank e' hr hr2
        (CFSG.RankThree.PartTwo.Census.le_localRank_PSL_torus (m := 3) hr
          (by rw [Nat.card_units, hK]; exact hrd) (by omega) (by omega) ?_))
      rcases h45 with rfl | rfl
      · exact Or.inr fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
          (hr.dvd_of_dvd_pow (show r ∣ 2 ^ 2 by simpa using h)))
      · exact Or.inl (by norm_num)
  · exact absurd hQT (not_evenRank_le_two_of_localRank e' Nat.prime_three (by norm_num)
      (three_le_localRank_PSL_of_six_le hn6))

theorem qtkSimpleList_of_psu_even {S : Type} [Group S] [Finite S] {n f : ℕ}
    (hQT : CFSG.Open.evenRank S ≤ 2) (hm : StatedClassicalModel S .PSU n 2 f) :
    QTKSimpleList S := by
  obtain ⟨⟨-, hf, hn, h32⟩, K, _, _, hK, ⟨e⟩⟩ := id hm
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : CharP K 2 := hU.charP
  rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | rfl | hn6
  · have hf2 : 2 ≤ f := by
      by_contra h
      exact h32 (by rw [show f = 1 by omega]; rfl)
    exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inl ⟨hf2, hm⟩))⟩)))
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hf, hm⟩))))⟩)))
  · by_cases hf2 : f = 2
    · subst hf2
      exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hm))))
    · obtain ⟨r, hr, hr2, hr5, hrd⟩ := exists_prime_ne_five_dvd_two_pow_add_one hf hf2
      exact absurd hQT (not_evenRank_le_two_of_localRank e hr hr2
        (CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus hU (k := 2) hr hrd
          (by norm_num) (Or.inr fun h => hr5 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).1 h))))
  · obtain ⟨r, hr, hr2, hrd⟩ :=
      CFSG.RankThree.PartTwo.Census.exists_odd_prime_dvd_two_pow_add_one hf
    exact absurd hQT (not_evenRank_le_two_of_localRank e hr hr2
      (CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus hU (k := 2) hr hrd (by omega)
        (Or.inl (by omega))))

end CFSG.SectionRank.QTK
