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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.BrauerLinearThree

namespace TenArith

theorem chi_one_same_false {q e A Y m : ℤ} (he : e = 1 ∨ e = -1) (hA : A = 9 ∨ A = 5)
    (hq : 7 ≤ q) (hY : Y ≠ 0) (hm : 2 * m = q + e)
    (h : 3 * (2 * q * (q ^ 2 - 1)) * Y * (q + e) = A * m * (2 * (q + e)) ^ 2 * q * Y) :
    False := by
  have hqe : 0 < q + e := by rcases he with rfl | rfl <;> omega
  have h' : 2 * q * Y * (q + e) * (3 * (q - e) * (q + e) - A * (q + e) ^ 2) = 0 := by
    rcases he with rfl | rfl
    · linear_combination h + 2 * A * q * Y * (q + 1) ^ 2 * hm
    · linear_combination h + 2 * A * q * Y * (q + -1) ^ 2 * hm
  have hne : 2 * q * Y * (q + e) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by omega) hY) (by omega)
  have h0 := (mul_eq_zero.mp h').resolve_left hne
  have h1 : (q + e) * (3 * (q - e) - A * (q + e)) = 0 := by linear_combination h0
  have h2 := (mul_eq_zero.mp h1).resolve_left (by omega)
  rcases he with rfl | rfl <;> rcases hA with rfl | rfl <;> omega

theorem chi_two_opposite_false {q f δ A u v k : ℤ} {n : ℕ} (hn : 4 ≤ n) (hδ : δ = 1 ∨ δ = -1)
    (hA : Odd A) (hu : Odd u) (hqv : q + 1 = 2 ^ (n - 2) * v)
    (hqu : q - 1 = 2 * u) (hf : f = δ * q + 2 ^ n * k)
    (h : 3 * (q + 1) ^ 2 * (f + δ) = A * (q - 1) ^ 2 * (f - δ)) : False := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
  have e2 : (2 : ℤ) ^ (j + 4 - 2) = 4 * 2 ^ j := by
    rw [show j + 4 - 2 = j + 2 by omega, pow_add]
    ring
  have e4 : (2 : ℤ) ^ (j + 4) = 16 * 2 ^ j := by
    rw [pow_add]
    ring
  rw [e2] at hqv
  rw [e4] at hf
  have h1 : (q + 1) ^ 2 = 16 * (2 ^ j) ^ 2 * v ^ 2 := by rw [hqv]; ring
  have h2 : (q - 1) ^ 2 = 4 * u ^ 2 := by rw [hqu]; ring
  have h3 : f + δ = 4 * 2 ^ j * (δ * v + 4 * k) := by rw [hf]; linear_combination δ * hqv
  have h4 : f - δ = 2 * (δ * u + 8 * 2 ^ j * k) := by rw [hf]; linear_combination δ * hqu
  rw [h1, h2, h3, h4] at h
  have key : 8 * (A * u ^ 2 * (δ * u + 8 * 2 ^ j * k)) =
      8 * (2 * (12 * (2 ^ j) ^ 3 * v ^ 2 * (δ * v + 4 * k))) := by
    linear_combination -h
  have key' := Int.eq_of_mul_eq_mul_left (by norm_num) key
  have hodd : Odd (A * u ^ 2 * (δ * u + 8 * 2 ^ j * k)) := by
    have hδu : Odd (δ * u) := by rcases hδ with rfl | rfl <;> simpa using hu
    have heven : Even (8 * 2 ^ j * k) := ⟨4 * 2 ^ j * k, by ring⟩
    exact (hA.mul hu.pow).mul (hδu.add_even heven)
  rw [key'] at hodd
  exact (Int.not_even_iff_odd.mpr hodd) (even_two_mul _)

theorem chi_three_same_false {g c' A m f δ y : ℤ} {n : ℕ} (hn : 4 ≤ n) (hg : Odd g)
    (hy : Odd y) (hfy : f + δ = 2 ^ (n - 1) * y)
    (h : 3 * (2 ^ n * g) * (f + δ) ^ 2 = A * m * (2 ^ n * c') ^ 2 * f * (f + δ)) : False := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [show j + 1 - 1 = j by omega] at hfy
  rw [hfy] at h
  have e1 : (2 : ℤ) ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  rw [e1] at h
  have hy0 : y ≠ 0 := fun h0 => by rw [h0] at hy; exact absurd hy (by decide)
  have hne : 2 * (2 : ℤ) ^ j * 2 ^ j * 2 ^ j * y ≠ 0 :=
    mul_ne_zero (by positivity) hy0
  have key : (2 * (2 : ℤ) ^ j * 2 ^ j * 2 ^ j * y) *
      (3 * g * y - 2 * (A * m * c' ^ 2 * f)) = 0 := by
    linear_combination h
  have h0 := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)
  have hodd : Odd (3 * g * y) := ((by decide : Odd (3 : ℤ)).mul hg).mul hy
  rw [h0] at hodd
  exact (Int.not_even_iff_odd.mpr hodd) (even_two_mul _)

theorem chi_one_nineteen_false {f₁ f₂ f₃ δ₁ δ₂ δ₃ : ℤ}
    (hsigns : (δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1))
    (hf₁ : 1 < f₁)
    (hsum : 1 + δ₁ * f₁ + δ₂ * f₂ + δ₃ * f₃ = 0) (hprod : f₁ * f₂ = 19 ^ 2 * f₃)
    (h : 3 * (2 * 19 * (19 ^ 2 - 1)) * (f₁ * (f₁ + δ₁)) * (19 + -1) =
      5 * 9 * (2 * (19 + -1)) ^ 2 * 19 * (f₁ * (f₁ - δ₁))) : False := by
  have hf₁0 : f₁ ≠ 0 := by omega
  have h' : f₁ * (738720 * (f₁ + δ₁) - 1108080 * (f₁ - δ₁)) = 0 := by linear_combination h
  have h'' := (mul_eq_zero.mp h').resolve_left hf₁0
  norm_num at hprod
  rcases hsigns with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · omega
  · omega
  · have hf5 : f₁ = 5 := by omega
    subst hf5
    omega

end TenArith

end CFSG.BrauerLinearThree
