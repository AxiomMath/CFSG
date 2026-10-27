module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeArithmeticBasic

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeArithmetic

theorem degreeG_two_not_integer (q : ℤ) (hq : 4 ≤ q) :
    ¬ ∃ m : ℤ, degreeG 2 q = (m : ℚ) := by
  rintro ⟨m, hm⟩
  have hqQ : (4 : ℚ) ≤ q := by exact_mod_cast hq
  have hden : (q : ℚ) + 1 ≠ 0 := by linarith
  have hNQ : ((q : ℚ) ^ 2 + 1) *
      ((q : ℚ) ^ 2 * ((q : ℚ) - 1) + q + 1) = ((q : ℚ) + 1) * m := by
    unfold degreeG at hm
    have hcross := (div_eq_iff hden).mp hm
    simpa only [mul_comm] using hcross
  have hN : (q ^ 2 + 1) * (q ^ 2 * (q - 1) + q + 1) = (q + 1) * m := by
    exact_mod_cast hNQ
  let c : ℤ := q ^ 4 - 2 * q ^ 3 + 4 * q ^ 2 - 4 * q + 5
  have hdivision : (q ^ 2 + 1) * (q ^ 2 * (q - 1) + q + 1) =
      (q + 1) * c - 4 := by
    dsimp [c]
    ring
  have hd : q + 1 ∣ (4 : ℤ) := by
    refine ⟨c - m, ?_⟩
    calc
      4 = (q + 1) * c - (q ^ 2 + 1) * (q ^ 2 * (q - 1) + q + 1) := by
        linarith [hdivision]
      _ = (q + 1) * (c - m) := by rw [hN]; ring
  have hle := Int.le_of_dvd (by norm_num : (0 : ℤ) < 4) hd
  omega

@[expose] def degreeGThreeInteger (q : ℤ) : ℤ := q ^ 6 - 2 * q ^ 5 + 2 * q ^ 4 + 1

theorem degreeG_three_eq_integer (q : ℤ) (hq : 4 ≤ q) :
    degreeG 3 q = (degreeGThreeInteger q : ℚ) := by
  rw [degreeG_three q hq]
  simp only [degreeGThreeInteger, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_pow, Int.cast_one, Int.cast_ofNat]

theorem degreeG_three_minus_two_not_dvd (q : ℤ) (hq : 4 ≤ q) :
    ¬ q ^ 2 - 1 ∣ degreeGThreeInteger q - 2 := by
  let c : ℤ := q ^ 4 - 2 * q ^ 3 + 3 * q ^ 2 - 2 * q + 3
  have hdivision : degreeGThreeInteger q - 2 =
      (q ^ 2 - 1) * c - 2 * (q - 1) := by
    dsimp [degreeGThreeInteger, c]
    ring
  intro hd
  have hrem : q ^ 2 - 1 ∣ 2 * (q - 1) := by
    have hsub := dvd_sub (dvd_mul_right (q ^ 2 - 1) c) hd
    have heq : (q ^ 2 - 1) * c - (degreeGThreeInteger q - 2) =
        2 * (q - 1) := by linarith [hdivision]
    rwa [heq] at hsub
  have hpos : (0 : ℤ) < 2 * (q - 1) := by omega
  have hsmall : 2 * (q - 1) < q ^ 2 - 1 := by nlinarith
  have hle := Int.le_of_dvd hpos hrem
  omega

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeArithmetic
