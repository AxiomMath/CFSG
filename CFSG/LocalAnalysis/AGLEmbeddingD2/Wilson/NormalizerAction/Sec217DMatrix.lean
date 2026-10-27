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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

abbrev M2 : Type := ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3

@[expose] def ap (A : M2) (x : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (A.1 * x.1 + A.2.1 * x.2, A.2.2.1 * x.1 + A.2.2.2 * x.2)

@[expose] def mm (A B : M2) : M2 :=
  (A.1 * B.1 + A.2.1 * B.2.2.1, A.1 * B.2.1 + A.2.1 * B.2.2.2,
    A.2.2.1 * B.1 + A.2.2.2 * B.2.2.1, A.2.2.1 * B.2.1 + A.2.2.2 * B.2.2.2)

@[expose] def m1 : M2 := (1, 0, 0, 1)

@[expose] def matOf (f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3) : M2 :=
  ((f (1, 0)).1, (f (0, 1)).1, (f (1, 0)).2, (f (0, 1)).2)

theorem ap_mm (A B : M2) (x : ZMod 3 × ZMod 3) : ap (mm A B) x = ap A (ap B x) := by
  simp only [ap, mm]
  ext <;> simp <;> ring

theorem ap_m1 (x : ZMod 3 × ZMod 3) : ap m1 x = x := by
  simp [ap, m1]

theorem ap_inj {A B : M2} (h : ∀ x, ap A x = ap B x) : A = B := by
  have h1 := h (1, 0)
  have h2 := h (0, 1)
  simp only [ap, mul_one, mul_zero, add_zero, zero_add, Prod.mk.injEq] at h1 h2
  obtain ⟨p, q, r, s⟩ := A
  obtain ⟨p', q', r', s'⟩ := B
  simp_all

theorem eq_ap_matOf {f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3}
    (hf : ∀ x y, f (x + y) = f x + f y) (x : ZMod 3 × ZMod 3) : f x = ap (matOf f) x := by
  let φ : ZMod 3 × ZMod 3 →+ ZMod 3 × ZMod 3 := AddMonoidHom.mk' f hf
  have hx : x = x.1.val • ((1 : ZMod 3), (0 : ZMod 3)) + x.2.val • ((0 : ZMod 3), (1 : ZMod 3)) := by
    ext <;> simp
  have : f x = x.1.val • f (1, 0) + x.2.val • f (0, 1) := by
    have h := map_add φ (x.1.val • ((1 : ZMod 3), (0 : ZMod 3)))
      (x.2.val • ((0 : ZMod 3), (1 : ZMod 3)))
    rw [map_nsmul, map_nsmul, ← hx] at h
    exact h
  rw [this]
  simp only [ap, matOf]
  ext <;> simp [nsmul_eq_mul]
  · ring
  · ring

theorem iterate_ap_two (V : M2) (hV : ∀ x, ap V (ap V x) = x) (k : ℕ) (hk : Odd k)
    (x : ZMod 3 × ZMod 3) : (ap V)^[k] x = ap V x := by
  obtain ⟨m, rfl⟩ := hk
  have h2 : (ap V)^[2] = id := funext hV
  rw [Function.iterate_add_apply, Function.iterate_mul, h2, Function.iterate_id]
  rfl

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem core_check : ∀ U V : M2, ap U (1, 0) = (1, 0) → ap U (0, 1) ≠ (0, 1) →
    (∀ x, (ap U)^[8] x = x) → ap V (0, 1) = (0, 1) → ap V (1, 0) ≠ (1, 0) →
    (∀ x, (ap V)^[8] x = x) →
    ((ap (mm U V) (1, 0)).2 = 0 → mm U V = m1) → ((ap (mm U V) (0, 1)).1 = 0 → mm U V = m1) →
    ((ap (mm (mm U V) (mm U V)) (1, 0)).2 = 0 → mm (mm U V) (mm U V) = m1) →
    ((ap (mm (mm U V) (mm U V)) (0, 1)).1 = 0 → mm (mm U V) (mm U V) = m1) →
    ∃ d : ZMod 3 × ZMod 3, d ≠ 0 ∧ ap (mm U V) d = d ∧
      (∃ v : ZMod 3 × ZMod 3, ap (mm U V) v = v + d) ∧
        ∀ v : ZMod 3 × ZMod 3, ∃ k : ZMod 3, ap (mm U V) v = v + (k * d.1, k * d.2) := by
  decide +kernel

theorem involution_check : ∀ V : M2, ap V (0, 1) = (0, 1) → ap V (1, 0) ≠ (1, 0) →
    (∀ x, (ap V)^[8] x = x) → ∀ x, ap V (ap V x) = x := by
  decide +kernel

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
