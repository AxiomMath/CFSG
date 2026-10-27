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

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionTwoAdic

theorem odd_cofactor_divisibility (d c : ℤ) (hd : d ≠ 0) (hc : Odd c) :
    d ∣ d * c ∧ ¬ 2 * d ∣ d * c := by
  refine ⟨dvd_mul_right d c, ?_⟩
  rintro ⟨k, hk⟩
  have heq : c = 2 * k := mul_left_cancel₀ hd (by
    calc
      d * c = (2 * d) * k := hk
      _ = d * (2 * k) := by ring)
  have heven : Even c := even_iff_two_dvd.mpr ⟨k, heq⟩
  have hodd : c % 2 = 1 := Int.odd_iff.mp hc
  have heven' : c % 2 = 0 := Int.even_iff.mp heven
  omega

theorem two_power_coprime_three (e : ℕ) : IsCoprime ((2 : ℤ) ^ e) 3 :=
  (by norm_num : IsCoprime (2 : ℤ) 3).pow_left

end CFSG.ProperTwoGeneratedCore.LocalCriterionTwoAdic
