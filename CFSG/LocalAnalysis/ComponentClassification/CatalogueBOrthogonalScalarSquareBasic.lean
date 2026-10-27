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
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

open LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem multiplier_square (B : _root_.LinearMap.BilinForm K V) (hB : B ≠ 0)
    (A : V ≃ₗ[K] V) (d μ : K)
    (hsquare : ∀ x : V, A (A x) = d • x)
    (hsim : ∀ x y : V, B (A x) (A y) = μ * B x y) : μ ^ 2 = d ^ 2 := by
  classical
  have hex : ∃ x y : V, B x y ≠ 0 := by
    by_contra h
    push Not at h
    apply hB
    ext x y
    exact h x y
  obtain ⟨x, y, hxy⟩ := hex
  have h := hsim (A x) (A y)
  rw [hsquare, hsquare, BilinForm.smul_left, BilinForm.smul_right, hsim] at h
  apply mul_right_cancel₀ hxy
  simpa only [pow_two, mul_assoc] using h.symm

theorem multiplier_ratio_sign (B : _root_.LinearMap.BilinForm K V) (hB : B ≠ 0)
    (A : V ≃ₗ[K] V) (d μ : K) (hd : d ≠ 0)
    (hsquare : ∀ x : V, A (A x) = d • x)
    (hsim : ∀ x y : V, B (A x) (A y) = μ * B x y) :
    μ / d = 1 ∨ μ / d = -1 := by
  apply sq_eq_one_iff.mp
  rw [div_pow, multiplier_square B hB A d μ hsquare hsim, div_self (pow_ne_zero _ hd)]

theorem scalar_square_adjoint (B : _root_.LinearMap.BilinForm K V) (A : V ≃ₗ[K] V)
    (d μ : K) (hd : d ≠ 0)
    (hsquare : ∀ x : V, A (A x) = d • x)
    (hsim : ∀ x y : V, B (A x) (A y) = μ * B x y) (x y : V) :
    B (A x) y = (μ / d) * B x (A y) := by
  have h := hsim x (A y)
  rw [hsquare, BilinForm.smul_right] at h
  calc
    B (A x) y = d⁻¹ * (d * B (A x) y) := by
      rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
    _ = d⁻¹ * (μ * B x (A y)) := by rw [h]
    _ = (μ / d) * B x (A y) := by rw [div_eq_mul_inv]; ring

theorem opposite_eigenspaces_orthogonal (B : _root_.LinearMap.BilinForm K V)
    (T : Module.End K V)
    (b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hadj : ∀ x y : V, B (T x) y = B x (T y))
    (x y : V) (hx : x ∈ T.eigenspace b) (hy : y ∈ T.eigenspace (-b)) :
    B x y = 0 := by
  have h := hadj x y
  rw [Module.End.mem_eigenspace_iff.mp hx, Module.End.mem_eigenspace_iff.mp hy,
    BilinForm.smul_left, BilinForm.smul_right] at h
  have hz : (2 * b) * B x y = 0 := by linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero h2 hb)

theorem same_eigenspace_isotropic (B : _root_.LinearMap.BilinForm K V)
    (T : Module.End K V)
    (b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hadj : ∀ x y : V, B (T x) y = -B x (T y))
    (x y : V) (hx : x ∈ T.eigenspace b) (hy : y ∈ T.eigenspace b) :
    B x y = 0 := by
  have h := hadj x y
  rw [Module.End.mem_eigenspace_iff.mp hx, Module.End.mem_eigenspace_iff.mp hy,
    BilinForm.smul_left, BilinForm.smul_right] at h
  have hz : (2 * b) * B x y = 0 := by linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero h2 hb)

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
