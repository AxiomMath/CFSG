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

namespace CFSG.LocalAnalysis.GLTheoremA

theorem suzukiD_exp (m : ℕ) :
    (1 + 2 ^ m) * 2 ^ (m + 1) = 2 ^ m + (1 + 2 ^ m) + (2 ^ (2 * m + 1) - 1) := by
  have h1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  have ht : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have hq : 2 ^ (2 * m + 1) = 2 ^ m * 2 ^ (m + 1) := by
    rw [← pow_add]; congr 1; omega
  have hA : (1 + 2 ^ m) * 2 ^ (m + 1) + 1 =
      2 ^ m + (1 + 2 ^ m) + 2 ^ (2 * m + 1) := by rw [hq, ht]; ring
  have hsub : (1 + 2 ^ m) * 2 ^ (m + 1) =
      (2 ^ m + (1 + 2 ^ m) + 2 ^ (2 * m + 1)) - 1 := Nat.eq_sub_of_add_eq hA
  rw [hsub, Nat.add_sub_assoc h1]

end CFSG.LocalAnalysis.GLTheoremA
