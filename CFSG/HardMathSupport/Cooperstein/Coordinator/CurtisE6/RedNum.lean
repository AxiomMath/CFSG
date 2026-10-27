module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

theorem window_numerics {n δ m g : ℕ} (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hgn : g ∣ n) (hgδ : g ∣ δ)
    (hg : 1 ≤ g) (h : (n / g = 1 ∧ 79 ≤ m) ∨ (2 ≤ n / g ∧ 78 * (n / g) + 2 ≤ m)) :
    (n = 1 → 79 ≤ δ * m) ∧ (2 ≤ n → 78 * n + 2 ≤ δ * m) := by
  obtain ⟨a, rfl⟩ := hgn
  have ha : g * a / g = a := Nat.mul_div_cancel_left a hg
  have hgδ' : g ≤ δ := Nat.le_of_dvd hδ hgδ
  rw [ha] at h
  have hapos : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0; simp at hn
    · exact h0
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1
    refine ⟨fun hn1 => ?_, fun hn2 => ?_⟩
    · calc 79 ≤ m := h2
        _ = 1 * m := (one_mul m).symm
        _ ≤ δ * m := Nat.mul_le_mul hδ le_rfl
    · have : 2 ≤ g := by omega
      calc 78 * (g * 1) + 2 ≤ δ * 79 := by nlinarith
        _ ≤ δ * m := Nat.mul_le_mul le_rfl h2
  · refine ⟨fun hn1 => ?_, fun hn2 => ?_⟩
    · exfalso
      have : g * a = 1 := hn1
      have h3 : a = 1 := by nlinarith
      omega
    · calc 78 * (g * a) + 2 ≤ g * (78 * a + 2) := by nlinarith
        _ ≤ δ * m := Nat.mul_le_mul hgδ' h2

theorem surv27_contra {n δ f a : ℕ} (hn : n ≤ δ) (hA : a * (2 ^ n) ^ f < (2 ^ n) ^ 27)
    (hoff : 2 ^ (δ * 27) ≤ a * 2 ^ (δ * f)) : False := by
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0; simp at hoff
    · exact h0
  have hf : f < 27 := by
    by_contra hf
    have : (2 ^ n) ^ 27 ≤ (2 ^ n) ^ f :=
      Nat.pow_le_pow_right (Nat.one_le_two_pow) (by omega)
    exact absurd (lt_of_le_of_lt (this.trans (Nat.le_mul_of_pos_left _ ha0)) hA) (lt_irrefl _)
  obtain ⟨r, hr⟩ : ∃ r, 27 = f + r := ⟨27 - f, by omega⟩
  have hr1 : 1 ≤ r := by omega
  rw [hr, pow_add] at hA
  have h1 : a < (2 ^ n) ^ r := by
    have hpos : 0 < (2 ^ n) ^ f := by positivity
    refine Nat.lt_of_mul_lt_mul_right (a := (2 ^ n) ^ f) ?_
    rw [mul_comm ((2 ^ n) ^ r)]
    exact hA
  rw [hr, mul_add, pow_add] at hoff
  have h2 : 2 ^ (δ * r) ≤ a := by
    have hpos : 0 < 2 ^ (δ * f) := by positivity
    rw [mul_comm] at hoff
    exact Nat.le_of_mul_le_mul_right hoff hpos
  have h3 : 2 ^ (δ * r) < 2 ^ (n * r) := by
    calc 2 ^ (δ * r) ≤ a := h2
      _ < (2 ^ n) ^ r := h1
      _ = 2 ^ (n * r) := by rw [← pow_mul]
  have h4 : δ * r < n * r := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h3
  have h5 : δ < n := Nat.lt_of_mul_lt_mul_right h4
  omega

theorem surv78_contra {n δ f a : ℕ} (hn : n ≤ δ) (hδ : 1 ≤ δ) (hf : 22 + f ≤ 78)
    (ha : a ≤ (2 ^ n) ^ 16) (hoff : 2 ^ (δ * 78) ≤ 2 * a * 2 ^ (δ * f)) : False := by
  have h1 : 2 ^ (δ * 78) ≤ 2 ^ (1 + 16 * n + δ * f) := by
    calc 2 ^ (δ * 78) ≤ 2 * a * 2 ^ (δ * f) := hoff
      _ ≤ 2 * (2 ^ n) ^ 16 * 2 ^ (δ * f) := by gcongr
      _ = 2 ^ (1 + 16 * n + δ * f) := by
        rw [← pow_mul, pow_add, pow_add, pow_one]; ring_nf
  have h2 : δ * 78 ≤ 1 + 16 * n + δ * f := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have h3 : δ * f ≤ δ * 56 := Nat.mul_le_mul le_rfl (by omega)
  nlinarith

theorem surv78_single {δ f : ℕ} (hδ : 1 ≤ δ) (hf : f ≤ 77)
    (hoff : 2 ^ (δ * 78) ≤ 2 * 2 ^ (δ * f)) : δ = 1 := by
  have h1 : 2 ^ (δ * 78) ≤ 2 ^ (1 + δ * f) := by
    calc 2 ^ (δ * 78) ≤ 2 * 2 ^ (δ * f) := hoff
      _ = 2 ^ (1 + δ * f) := by rw [pow_add, pow_one]
  have h2 : δ * 78 ≤ 1 + δ * f := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have h3 : δ * f ≤ δ * 77 := Nat.mul_le_mul le_rfl hf
  omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
