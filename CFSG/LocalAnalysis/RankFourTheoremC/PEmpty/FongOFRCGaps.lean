module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCStepGen
import CFSG.LieType.SeitzGeneration.ExcTorusE6Five
import CFSG.LieType.SeitzGeneration.ExcTorusE7Five
import CFSG.LieType.SeitzGeneration.ExcTorusE7Eight
import CFSG.LieType.SeitzGeneration.ExcTorusE7Ten
import CFSG.LieType.SeitzGeneration.ExcTorusE7Twelve
import CFSG.LieType.SeitzGeneration.ExcTorusE8Seven
import CFSG.LieType.SeitzGeneration.ExcTorusE8Nine
import CFSG.LieType.SeitzGeneration.ExcTorusE8Fourteen
import CFSG.LieType.SeitzGeneration.ExcTorusE8Eighteen
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Shared
import CFSG.RankThree.PartOne.KE.CTCasesCycloGlue

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.Chevalley (exhaustionPhi)
open CFSG.RankThree.PartOne.KE.CTCyclo (key_data cycloIdx)

theorem orderOf_eq_nine_of_dvd_phi {p q : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (h : (p : ℤ) ∣ (exhaustionPhi 9).eval (q : ℤ)) : orderOf (q : ZMod p) = 9 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hz : (((exhaustionPhi 9).eval (q : ℤ) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h
  simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one, Int.cast_add, Int.cast_pow, Int.cast_one, Int.cast_natCast] at hz
  set x : ZMod p := (q : ZMod p) with hx
  have h9 : x ^ 9 = 1 := by
    have : x ^ 9 - 1 = (x ^ 3 - 1) * (x ^ 6 + x ^ 3 + 1) := by ring
    rw [hz, mul_zero] at this
    exact sub_eq_zero.1 this
  have hd9 : orderOf x ∣ 9 := orderOf_dvd_of_pow_eq_one h9
  have h3 : ¬ orderOf x ∣ 3 := by
    intro h3d
    have hx3 : x ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 h3d
    have : (3 : ZMod p) = 0 := by
      have h6 : x ^ 6 = 1 := by rw [show 6 = 3 * 2 by rfl, pow_mul, hx3, one_pow]
      rw [h6, hx3] at hz
      linear_combination hz
    have h3p : p ∣ 3 := by
      have := (ZMod.natCast_eq_zero_iff 3 p).1 (by exact_mod_cast this)
      exact this
    have := Nat.le_of_dvd (by norm_num) h3p
    omega
  obtain ⟨k, hk, hk9⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (by simpa using hd9 :
    orderOf x ∣ 3 ^ 2)
  interval_cases k
  · exact absurd (by simp [hk9]) h3
  · exact absurd (by simp [hk9]) h3
  · simpa [hk9]

theorem orderOf_eq_eighteen_of_dvd_phi {p q : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (h : (p : ℤ) ∣ (exhaustionPhi 18).eval (q : ℤ)) : orderOf (q : ZMod p) = 18 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hz : (((exhaustionPhi 18).eval (q : ℤ) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h
  simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one, Int.cast_add, Int.cast_sub, Int.cast_pow,
    Int.cast_one, Int.cast_natCast] at hz
  set x : ZMod p := (q : ZMod p) with hx
  have hp2 : (2 : ZMod p) ≠ 0 := by
    intro h2
    have h2p : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h2)
    have := Nat.le_of_dvd (by norm_num) h2p
    omega
  have hm9 : x ^ 9 = -1 := by
    have : x ^ 9 + 1 = (x ^ 3 + 1) * (x ^ 6 - x ^ 3 + 1) := by ring
    rw [hz, mul_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  have h18 : x ^ 18 = 1 := by
    rw [show 18 = 9 * 2 by rfl, pow_mul, hm9]
    exact neg_one_sq
  have hd : orderOf x ∣ 18 := orderOf_dvd_of_pow_eq_one h18
  have h9n : ¬ orderOf x ∣ 9 := by
    intro hd9
    have : x ^ 9 = 1 := orderOf_dvd_iff_pow_eq_one.1 hd9
    rw [hm9] at this
    exact hp2 (by rw [← one_add_one_eq_two]; exact neg_eq_iff_add_eq_zero.1 this)
  have h6n : ¬ orderOf x ∣ 6 := by
    intro hd6
    have hx6 : x ^ 6 = 1 := orderOf_dvd_iff_pow_eq_one.1 hd6
    have hx3 : x ^ 3 = 2 := by
      rw [hx6] at hz
      linear_combination -hz
    have : x ^ 6 = 4 := by
      rw [show 6 = 3 * 2 by rfl, pow_mul, hx3]
      norm_num
    rw [hx6] at this
    have h3 : (3 : ZMod p) = 0 := by linear_combination -this
    have h3p : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1 (by exact_mod_cast h3)
    have := Nat.le_of_dvd (by norm_num) h3p
    omega
  have hcases : orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 6 ∨ orderOf x = 9 ∨
      orderOf x = 18 := by
    have hmem : orderOf x ∈ Nat.divisors 18 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
    have : Nat.divisors 18 = {1, 2, 3, 6, 9, 18} := by decide
    rw [this] at hmem
    simpa using hmem
  rcases hcases with h1 | h1 | h1 | h1 | h1 | h1
  · exact absurd (by rw [h1]; norm_num) h6n
  · exact absurd (by rw [h1]; norm_num) h6n
  · exact absurd (by rw [h1]; norm_num) h6n
  · exact absurd (by rw [h1]) h6n
  · exact absurd (by rw [h1]) h9n
  · exact h1

section


theorem cyclicSylowGap_E6_five : CyclicSylowGap Tag.E6 5 := by
  intro K _ _ p hp hp7 h
  have he := (key_data hp hp7 (by simp [cycloIdx]) h).1
  exact CFSG.LocalAnalysis.GLTheoremA.pRank_le_of_sylowTorusDatum (sylowTorus_E6_five K hp he) hp

theorem cyclicSylowGap_E7_five : CyclicSylowGap Tag.E7 5 := by
  intro K _ _ p hp hp7 h
  have he := (key_data hp hp7 (by simp [cycloIdx]) h).1
  exact CFSG.LocalAnalysis.GLTheoremA.pRank_le_of_sylowTorusDatum (sylowTorus_E7_five K hp he) hp

theorem cyclicSylowGap_E7_eight : CyclicSylowGap Tag.E7 8 := by
  intro K _ _ p hp hp7 h
  have he := (key_data hp hp7 (by simp [cycloIdx]) h).1
  exact CFSG.LocalAnalysis.GLTheoremA.pRank_le_of_sylowTorusDatum (sylowTorus_E7_eight K hp he) hp

theorem cyclicSylowGap_E7_ten : CyclicSylowGap Tag.E7 10 := by
  intro K _ _ p hp hp7 h
  have he := (key_data hp hp7 (by simp [cycloIdx]) h).1
  exact CFSG.LocalAnalysis.GLTheoremA.pRank_le_of_sylowTorusDatum (sylowTorus_E7_ten K hp he) hp

theorem cyclicSylowGap_E7_twelve : CyclicSylowGap Tag.E7 12 := by
  intro K _ _ p hp hp7 h
  have he := (key_data hp hp7 (by simp [cycloIdx]) h).1
  exact CFSG.LocalAnalysis.GLTheoremA.pRank_le_of_sylowTorusDatum (sylowTorus_E7_twelve K hp he) hp

theorem cyclicSylowGap_E8_seven : CyclicSylowGap Tag.E8 7 := by
  intro K _ _ p hp hp7 h
  have he := (key_data hp hp7 (by simp [cycloIdx]) h).1
  exact CFSG.LocalAnalysis.GLTheoremA.pRank_le_of_sylowTorusDatum (sylowTorus_E8_seven K hp he) hp

theorem cyclicSylowGap_E8_nine : CyclicSylowGap Tag.E8 9 := by
  intro K _ _ p hp hp7 h
  have he := orderOf_eq_nine_of_dvd_phi hp hp7 h
  exact CFSG.LocalAnalysis.GLTheoremA.pRank_le_of_sylowTorusDatum (sylowTorus_E8_nine K hp he) hp

theorem cyclicSylowGap_E8_fourteen : CyclicSylowGap Tag.E8 14 := by
  intro K _ _ p hp hp7 h
  have he := (key_data hp hp7 (by simp [cycloIdx]) h).1
  exact CFSG.LocalAnalysis.GLTheoremA.pRank_le_of_sylowTorusDatum (sylowTorus_E8_fourteen K hp he) hp

theorem cyclicSylowGap_E8_eighteen : CyclicSylowGap Tag.E8 18 := by
  intro K _ _ p hp hp7 h
  have he := orderOf_eq_eighteen_of_dvd_phi hp hp7 h
  exact CFSG.LocalAnalysis.GLTheoremA.pRank_le_of_sylowTorusDatum (sylowTorus_E8_eighteen K hp he) hp

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
