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
public import Mathlib.Tactic.Basify
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
public import Mathlib.Topology.Sheaves.Init

public section

open scoped BigOperators Matrix

namespace CFSG.Wreathed.FlatComplete

theorem core_cases {z₀ z₁ z₂ z₃ w κ R N M : ℤ} (hM : 2 ≤ M) (hN : N ≤ 7) (hR : 0 ≤ R)
    (hX : z₀ + z₁ + z₂ + z₃ + 2 * κ = 0) (hY : z₀ + z₁ - z₂ - z₃ = 0)
    (hC : z₀ - z₁ + z₂ - z₃ + 2 * w = 6)
    (hn : z₀ * z₀ + z₁ * z₁ + z₂ * z₂ + z₃ * z₃ + w * w + M * (κ * κ) + R = N) :
    κ = 0 ∧ z₁ = -z₀ ∧ z₃ = -z₂ ∧
      ((z₀ = 1 ∧ z₂ = 1 ∧ w = 1 ∧ R = N - 5) ∨ (z₀ = 1 ∧ z₂ = 0 ∧ w = 2 ∧ R = N - 6) ∨
        (z₀ = 0 ∧ z₂ = 1 ∧ w = 2 ∧ R = N - 6)) := by
  have h1 : z₁ = -κ - z₀ := by omega
  have h3 : z₃ = -κ - z₂ := by omega
  have hw : w = 3 - z₀ - z₂ - κ := by omega
  subst h1 h3 hw
  have s0 := mul_self_nonneg z₀
  have s1 := mul_self_nonneg (-κ - z₀)
  have s2 := mul_self_nonneg z₂
  have s3 := mul_self_nonneg (-κ - z₂)
  have s4 := mul_self_nonneg (3 - z₀ - z₂ - κ)
  have sk := mul_self_nonneg κ
  have hMk : 2 * (κ * κ) ≤ M * (κ * κ) := mul_le_mul_of_nonneg_right hM sk
  have b0 : -2 ≤ z₀ ∧ z₀ ≤ 2 := by constructor <;> nlinarith
  have b2 : -2 ≤ z₂ ∧ z₂ ≤ 2 := by constructor <;> nlinarith
  have bk : -1 ≤ κ ∧ κ ≤ 1 := by constructor <;> nlinarith
  obtain ⟨b0l, b0u⟩ := b0
  obtain ⟨b2l, b2u⟩ := b2
  obtain ⟨bkl, bku⟩ := bk
  interval_cases z₀ <;> interval_cases z₂ <;> interval_cases κ <;> omega

theorem pair_cases {y₀ y₁ y₂ y₃ : ℤ} (h01 : y₀ + y₁ = 0) (h23 : y₂ + y₃ = 0)
    (hn : y₀ * y₀ + y₁ * y₁ + y₂ * y₂ + y₃ * y₃ = 2) :
    ((y₀ = 1 ∨ y₀ = -1) ∧ y₁ = -y₀ ∧ y₂ = 0 ∧ y₃ = 0) ∨
      (y₀ = 0 ∧ y₁ = 0 ∧ (y₂ = 1 ∨ y₂ = -1) ∧ y₃ = -y₂) := by
  have e1 : y₁ = -y₀ := by omega
  have e3 : y₃ = -y₂ := by omega
  subst e1 e3
  have b0 : -1 ≤ y₀ ∧ y₀ ≤ 1 := by constructor <;> nlinarith [mul_self_nonneg y₂]
  have b2 : -1 ≤ y₂ ∧ y₂ ≤ 1 := by constructor <;> nlinarith [mul_self_nonneg y₀]
  obtain ⟨b0l, b0u⟩ := b0
  obtain ⟨b2l, b2u⟩ := b2
  interval_cases y₀ <;> interval_cases y₂ <;> omega

theorem le_mul_self_int (a : ℤ) : a ≤ a * a := by
  rcases le_or_gt a 0 with h | h
  · nlinarith
  · nlinarith

theorem mul_le_mul_self_of_abs_le_one {a b : ℤ} (hb : -1 ≤ b ∧ b ≤ 1) : a * b ≤ a * a := by
  rcases le_or_gt a 0 with h | h
  · nlinarith
  · nlinarith [le_mul_self_int a]

theorem sign_mul_self {x : ℤ} (hx : x = 1 ∨ x = -1) : x * x = 1 := by
  rcases hx with rfl | rfl <;> norm_num

theorem sign_bounds {x : ℤ} (hx : x = 1 ∨ x = -1) : -1 ≤ x ∧ x ≤ 1 := by
  rcases hx with rfl | rfl <;> norm_num

@[expose] def caseZ0 : Fin 3 → ℤ := ![1, 1, 0]

@[expose] def caseZ2 : Fin 3 → ℤ := ![1, 0, 1]

@[expose] def caseW : Fin 3 → ℤ := ![1, 2, 2]

@[expose] def caseNorm : Fin 3 → ℤ := ![5, 6, 6]

theorem case_prod (a b : Fin 3) :
    caseZ0 a * caseZ0 b + caseZ0 a * caseZ0 b + caseZ2 a * caseZ2 b + caseZ2 a * caseZ2 b +
      caseW a * caseW b = if a = b then caseNorm a else 4 := by
  fin_cases a <;> fin_cases b <;> decide

theorem case_norm (a : Fin 3) :
    caseZ0 a * caseZ0 a + caseZ0 a * caseZ0 a + caseZ2 a * caseZ2 a + caseZ2 a * caseZ2 a +
      caseW a * caseW a = caseNorm a := by
  simpa using case_prod a a

theorem core_cases' {z₀ z₁ z₂ z₃ w κ R N M : ℤ} (hM : 2 ≤ M) (hN : N ≤ 7) (hR : 0 ≤ R)
    (hX : z₀ + z₁ + z₂ + z₃ + 2 * κ = 0) (hY : z₀ + z₁ - z₂ - z₃ = 0)
    (hC : z₀ - z₁ + z₂ - z₃ + 2 * w = 6)
    (hn : z₀ * z₀ + z₁ * z₁ + z₂ * z₂ + z₃ * z₃ + w * w + M * (κ * κ) + R = N) :
    κ = 0 ∧ ∃ a : Fin 3, z₀ = caseZ0 a ∧ z₁ = -caseZ0 a ∧ z₂ = caseZ2 a ∧ z₃ = -caseZ2 a ∧
      w = caseW a ∧ R = N - caseNorm a := by
  obtain ⟨hκ, h1, h3, hc⟩ := core_cases hM hN hR hX hY hC hn
  refine ⟨hκ, ?_⟩
  rcases hc with ⟨e0, e2, ew, eR⟩ | ⟨e0, e2, ew, eR⟩ | ⟨e0, e2, ew, eR⟩
  · exact ⟨0, e0, by rw [h1, e0]; rfl, e2, by rw [h3, e2]; rfl, ew, eR⟩
  · exact ⟨1, e0, by rw [h1, e0]; rfl, e2, by rw [h3, e2]; rfl, ew, eR⟩
  · exact ⟨2, e0, by rw [h1, e0]; rfl, e2, by rw [h3, e2]; rfl, ew, eR⟩

end CFSG.Wreathed.FlatComplete
