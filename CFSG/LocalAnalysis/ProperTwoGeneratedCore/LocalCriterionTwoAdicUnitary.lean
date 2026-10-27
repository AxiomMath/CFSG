module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTwoAdicBasic
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionTwoAdic

theorem unitary_involution_count_two_part (f : ℕ) (hf : 2 ≤ f)
    (n : ℤ) (_hn : 1 ≤ n)
    (hcount : (n : ℚ) - 1 = ((2 : ℚ) ^ f) ^ 3 *
      (((((2 : ℚ) ^ f) ^ 3 + 1) * ((2 : ℚ) ^ f - 1)) /
        (3 * ((2 : ℚ) ^ f + 1)) + 1)) :
    let q : ℤ := 2 ^ f
    2 * q ^ 3 ∣ n - 1 ∧ ¬ 4 * q ^ 3 ∣ n - 1 ∧ ¬ q ^ 4 ∣ n - 1 := by
  let q : ℤ := 2 ^ f
  change 2 * q ^ 3 ∣ n - 1 ∧ ¬ 4 * q ^ 3 ∣ n - 1 ∧ ¬ q ^ 4 ∣ n - 1
  have hqQ : (q : ℚ) = (2 : ℚ) ^ f := by simp [q]
  have hden : (2 : ℚ) ^ f + 1 ≠ 0 := by positivity
  have hquot :
      (((((2 : ℚ) ^ f) ^ 3 + 1) * ((2 : ℚ) ^ f - 1)) /
        (3 * ((2 : ℚ) ^ f + 1)) + 1) =
      (((2 : ℚ) ^ f) ^ 3 - 2 * ((2 : ℚ) ^ f) ^ 2 + 2 * (2 : ℚ) ^ f + 2) / 3 := by
    field_simp
    ring
  rw [hquot] at hcount
  have hpolyQ : (3 : ℚ) * ((n : ℚ) - 1) =
      (q : ℚ) ^ 3 * ((q : ℚ) ^ 3 - 2 * (q : ℚ) ^ 2 + 2 * (q : ℚ) + 2) := by
    rw [hqQ]
    field_simp at hcount
    nlinarith [hcount]
  have hpoly : 3 * (n - 1) = q ^ 3 * (q ^ 3 - 2 * q ^ 2 + 2 * q + 2) := by
    exact_mod_cast hpolyQ
  obtain ⟨g, hg⟩ : ∃ g : ℕ, f = g + 2 := ⟨f - 2, by omega⟩
  let c : ℤ := 2 ^ g
  have hq : q = 4 * c := by simp [q, hg, c, pow_add, mul_comm]
  let b : ℤ := 32 * c ^ 3 - 16 * c ^ 2 + 4 * c + 1
  have hb : Odd b := by
    refine ⟨16 * c ^ 3 - 8 * c ^ 2 + 2 * c, ?_⟩
    dsimp [b]
    ring
  have hfactor : 3 * (n - 1) = (2 * q ^ 3) * b := by
    rw [hpoly, hq]
    dsimp [b]
    ring
  have hqne : q ≠ 0 := by dsimp [q]; positivity
  have hdne : 2 * q ^ 3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hqne)
  obtain ⟨hd, hnot⟩ := odd_cofactor_divisibility (2 * q ^ 3) b hdne hb
  have hdthree : 2 * q ^ 3 ∣ 3 * (n - 1) := by rwa [hfactor]
  have hcoprime : IsCoprime (2 * q ^ 3) 3 :=
    (by norm_num : IsCoprime (2 : ℤ) 3).mul_left
      ((two_power_coprime_three f).pow_left)
  have hdiv : 2 * q ^ 3 ∣ n - 1 := hcoprime.dvd_of_dvd_mul_left hdthree
  have hnond : ¬ 4 * q ^ 3 ∣ n - 1 := by
    intro h
    have hthree : 4 * q ^ 3 ∣ 3 * (n - 1) := dvd_mul_of_dvd_right h 3
    apply hnot
    simpa only [show 2 * (2 * q ^ 3) = 4 * q ^ 3 by ring, hfactor] using hthree
  refine ⟨hdiv, hnond, ?_⟩
  intro h
  apply hnond
  have hdq : 4 * q ^ 3 ∣ q ^ 4 := by
    refine ⟨c, ?_⟩
    rw [hq]
    ring
  exact dvd_trans hdq h

end CFSG.ProperTwoGeneratedCore.LocalCriterionTwoAdic
