module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeArithmetic

@[expose] def degreeF (i : ℕ) (a : ℤ) : ℚ :=
  ((a : ℚ) ^ i + 1) * ((a : ℚ) ^ i * ((a : ℚ) - 1) + 1)

@[expose] def degreeG (i : ℕ) (a : ℤ) : ℚ :=
  ((a : ℚ) ^ i + 1) * ((a : ℚ) ^ i * ((a : ℚ) - 1) + a + 1) / (a + 1)

theorem degreeF_strictMono (a : ℤ) (ha : 4 ≤ a) : StrictMono (fun i => degreeF i a) := by
  have haQ : (4 : ℚ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℚ) < a := by linarith
  have ham : (0 : ℚ) < (a : ℚ) - 1 := by linarith
  intro i j hij
  have hp : (a : ℚ) ^ i < (a : ℚ) ^ j := pow_lt_pow_right₀ (by linarith) hij
  have hfactor : (a : ℚ) ^ i * ((a : ℚ) - 1) <
      (a : ℚ) ^ j * ((a : ℚ) - 1) := mul_lt_mul_of_pos_right hp (by linarith)
  unfold degreeF
  exact mul_lt_mul_of_pos (by linarith) (by linarith) (by positivity) (by positivity)

theorem degreeG_strictMono (a : ℤ) (ha : 4 ≤ a) : StrictMono (fun i => degreeG i a) := by
  have haQ : (4 : ℚ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℚ) < a := by linarith
  have ham : (0 : ℚ) < (a : ℚ) - 1 := by linarith
  intro i j hij
  have hp : (a : ℚ) ^ i < (a : ℚ) ^ j := pow_lt_pow_right₀ (by linarith) hij
  have hfactor : (a : ℚ) ^ i * ((a : ℚ) - 1) <
      (a : ℚ) ^ j * ((a : ℚ) - 1) := mul_lt_mul_of_pos_right hp (by linarith)
  unfold degreeG
  apply (div_lt_div_iff_of_pos_right (by linarith : (0 : ℚ) < a + 1)).mpr
  exact mul_lt_mul_of_pos (by linarith) (by linarith) (by positivity) (by positivity)

theorem degreeF_one (a : ℤ) : degreeF 1 a = (a : ℚ) ^ 3 + 1 := by
  unfold degreeF
  ring

theorem degreeG_one (a : ℤ) (ha : 4 ≤ a) : degreeG 1 a = (a : ℚ) ^ 2 + 1 := by
  have haQ : (4 : ℚ) ≤ a := by exact_mod_cast ha
  have hden : (a : ℚ) + 1 ≠ 0 := by linarith
  unfold degreeG
  field_simp
  ring

theorem degreeG_three (a : ℤ) (ha : 4 ≤ a) :
    degreeG 3 a = (a : ℚ) ^ 6 - 2 * (a : ℚ) ^ 5 + 2 * (a : ℚ) ^ 4 + 1 := by
  have haQ : (4 : ℚ) ≤ a := by exact_mod_cast ha
  have hden : (a : ℚ) + 1 ≠ 0 := by linarith
  unfold degreeG
  field_simp
  ring

theorem degree_exponent_chains (a : ℤ) (ha : 4 ≤ a) :
    degreeF 1 a < degreeF 2 a ∧ degreeF 2 a < degreeF 3 a ∧
      degreeG 1 a < degreeG 2 a ∧ degreeG 2 a < degreeG 3 a := by
  exact ⟨degreeF_strictMono a ha (by decide), degreeF_strictMono a ha (by decide),
    degreeG_strictMono a ha (by decide), degreeG_strictMono a ha (by decide)⟩

theorem degree_square_parameter_separation (q : ℤ) (hq : 4 ≤ q)
    (i j : ℕ) (hi : 1 ≤ i) (hj : j ≤ 3) : degreeG j q < degreeF i (q ^ 2) := by
  have hqQ : (4 : ℚ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℚ) < q := by linarith
  have hqm : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have hq2 : (4 : ℤ) ≤ q ^ 2 := by nlinarith
  have hf : degreeF 1 (q ^ 2) ≤ degreeF i (q ^ 2) :=
    (degreeF_strictMono (q ^ 2) hq2).monotone hi
  have hg : degreeG j q ≤ degreeG 3 q := (degreeG_strictMono q hq).monotone hj
  have hF : degreeF 1 (q ^ 2) = (q : ℚ) ^ 6 + 1 := by
    rw [degreeF_one, Int.cast_pow]
    ring
  have hG : degreeG 3 q = (q : ℚ) ^ 6 + 1 - 2 * (q : ℚ) ^ 4 * ((q : ℚ) - 1) := by
    rw [degreeG_three q hq]
    ring
  have hpos : (0 : ℚ) < 2 * (q : ℚ) ^ 4 * ((q : ℚ) - 1) := by positivity
  rw [hF] at hf
  rw [hG] at hg
  linarith

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeArithmetic
