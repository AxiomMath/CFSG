module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

public section

namespace CFSG.GH74.GLS.Stage4.Hex

variable {F : Type*} [Field F]

theorem solve_a4 (h2 : (2 : F) ≠ 0) (e : F) (a4 : F → F → F)
    (K1 : ∀ s s' t, a4 (s + s') t = a4 s' t + a4 s t)
    (K2 : ∀ s t t', a4 s (t + t') = a4 s t + (a4 s t' + t * (6 * e * (s * t'))))
    (K3 : ∀ τ : Fˣ, ∀ s t, a4 ((τ : F)⁻¹ * s) ((τ : F) * t) = (τ : F) * a4 s t) :
    ∀ s t, a4 s t = 3 * e * s * t ^ 2 := by
  intro s t
  have hτ := K3 (Units.mk0 2 h2) s t
  simp only [Units.val_mk0] at hτ
  have e1 := K1 (2⁻¹ * s) (2⁻¹ * s) t
  have e2 := K2 (2⁻¹ * s) t t
  have hs : (2⁻¹ * s + 2⁻¹ * s : F) = s := by field_simp; ring
  have ht : (2 : F) * t = t + t := by ring
  rw [hs] at e1
  rw [ht] at hτ
  have key : a4 s t = t * (6 * e * (2⁻¹ * s * t)) := by
    linear_combination (-1 : F) * hτ + e2 - e1
  rw [key]
  field_simp
  ring

theorem solve_A4 (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (e : F) (a4 A4 : F → F → F) (f₂ : F → F)
    (hf₂ : ∀ x y, f₂ (x + y) = f₂ x + f₂ y) (ha4 : ∀ s t, a4 s t = 3 * e * s * t ^ 2)
    (C1 : ∀ c c' s, A4 (c + c') s =
      A4 c' s + c * (e * c' * s ^ 3) + A4 c s + (c' * s) * (3 * e * c * s ^ 2))
    (C2 : ∀ c s s', A4 c (s + s') = A4 c s + (A4 c s' + a4 s (c * s') +
      (c * s) * (3 * e * c * s' ^ 2 + 6 * e * (s * (c * s')))))
    (C3 : ∀ τ : Fˣ, ∀ c s, A4 ((τ : F) ^ 2 * c) ((τ : F)⁻¹ * s) = (τ : F) * A4 c s)
    (W : ∀ s, f₂ (e * 1 * s ^ 3) + a4 (-s) s = A4 (-1) (-s)) :
    ∀ c s, A4 c s = 2 * e * c ^ 2 * s ^ 3 := by
  set B : F → F → F := fun c s => A4 c s - 2 * e * c ^ 2 * s ^ 3 with hB
  have hBc : ∀ c c' s, B (c + c') s = B c' s + B c s := by
    intro c c' s; simp only [hB]; rw [C1]; ring
  have hBs : ∀ c s s', B c (s + s') = B c s + B c s' := by
    intro c s s'; simp only [hB]; rw [C2, ha4]; ring
  have hBτ : ∀ τ : Fˣ, ∀ c s, B ((τ : F) ^ 2 * c) ((τ : F)⁻¹ * s) = (τ : F) * B c s := by
    intro τ c s
    have hτ := τ.ne_zero
    simp only [hB]; rw [C3]; field_simp
  have hB0 : ∀ s, B 0 s = 0 := by
    intro s; have := hBc 0 0 s; simp at this; linear_combination this
  have hBneg : ∀ c s, B (-c) s = - B c s := by
    intro c s; have := hBc (-c) c s; rw [neg_add_cancel, hB0] at this; linear_combination -this
  have hBs0 : ∀ c, B c 0 = 0 := by
    intro c; have := hBs c 0 0; simp at this; linear_combination this
  have hg : ∀ s, f₂ (e * s ^ 3) = e * s ^ 3 + B 1 s := by
    intro s
    have h := W s
    have hb : B (-1) (-s) = B 1 s := by
      have h1 := hBs (-1) s (-s)
      rw [add_neg_cancel, hBs0, hBneg 1 s] at h1
      linear_combination (-1 : F) * h1
    have hA : A4 (-1) (-s) = B (-1) (-s) + 2 * e * (-1) ^ 2 * (-s) ^ 3 := by
      simp only [hB]; ring
    simp only [mul_one] at h
    rw [ha4, hA, hb] at h
    linear_combination h
  have hf2 : ∀ x, f₂ (2 * x) = 2 * f₂ x := by
    intro x; rw [two_mul, two_mul]; exact hf₂ x x
  have h6ne : (6 : F) ≠ 0 := by
    have : (6 : F) = 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero h2 h3
  have hg0 : ∀ s, B 1 s = 0 := by
    intro s
    have h1 := hg (2 * s)
    have h2' : f₂ (e * (2 * s) ^ 3) = 8 * f₂ (e * s ^ 3) := by
      have : e * (2 * s) ^ 3 = 2 * (2 * (2 * (e * s ^ 3))) := by ring
      rw [this, hf2, hf2, hf2]; ring
    have h3' : B 1 (2 * s) = 2 * B 1 s := by rw [two_mul, hBs]; ring
    rw [hg s] at h2'
    have h6 : (6 : F) * B 1 s = 0 := by linear_combination h3' - h2' + h1
    exact (mul_eq_zero.1 h6).resolve_left h6ne
  have hsq : ∀ x s, B (x ^ 2) s = 0 := by
    intro x s
    by_cases hx : x = 0
    · subst hx; simp [hB0]
    · have h := hBτ (Units.mk0 x hx) 1 (x * s)
      simp only [Units.val_mk0] at h
      rw [show x⁻¹ * (x * s) = s by field_simp, hg0, mul_zero, mul_one] at h
      exact h
  intro c s
  have hc : ((c + 1) / 2) ^ 2 + (-(((c - 1) / 2) ^ 2)) = c := by field_simp; ring
  have key := hBc (((c + 1) / 2) ^ 2) (-(((c - 1) / 2) ^ 2)) s
  rw [hc, hBneg, hsq, hsq] at key
  simp only [hB] at key
  linear_combination key

end CFSG.GH74.GLS.Stage4.Hex
