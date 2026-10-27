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

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

theorem degree_identity_of_moving_count (n k a : ℚ)
    (hmove : n - k = k * (k - 1) * a) :
    n - 1 = (k - 1) * (k * a + 1) := by
  calc
    n - 1 = (n - k) + (k - 1) := by ring
    _ = k * (k - 1) * a + (k - 1) := by rw [hmove]
    _ = (k - 1) * (k * a + 1) := by ring

theorem degree_identity_power_substitution
    (n k : ℕ) (a : ℚ)
    (hdegree : (n : ℚ) - 1 = ((k : ℚ) - 1) * ((k : ℚ) * a + 1))
    (q i : ℕ) (hk : k = q ^ i + 1) :
    (n : ℚ) - 1 = (q : ℚ) ^ i * (((q : ℚ) ^ i + 1) * a + 1) := by
  rw [hk, Nat.cast_add, Nat.cast_pow, Nat.cast_one] at hdegree
  simpa only [add_sub_cancel_right] using hdegree

theorem degree_identity_integer_power_substitution
    (n k : ℕ) (a : ℚ)
    (hdegree : (n : ℚ) - 1 = ((k : ℚ) - 1) * ((k : ℚ) * a + 1))
    (q : ℤ) (i : ℕ) (hk : (k : ℤ) = q ^ i + 1) :
    (n : ℚ) - 1 = (q : ℚ) ^ i * (((q : ℚ) ^ i + 1) * a + 1) := by
  have hkQ : (k : ℚ) = (q : ℚ) ^ i + 1 := by exact_mod_cast hk
  rw [hkQ] at hdegree
  simpa only [add_sub_cancel_right] using hdegree

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
