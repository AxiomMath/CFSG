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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix

section Hilbert

variable {K F : Type} [Field K] [Field F] [Fintype F] (ι : F →+* K) (σ : K ≃+* K)

theorem map_smul_ringEquiv (c : K) (M : Matrix (Fin 3) (Fin 3) K) :
    (c • M).map σ = σ c • M.map σ := by
  ext i j
  simp

theorem map_add_ringEquiv (M N : Matrix (Fin 3) (Fin 3) K) :
    (M + N).map σ = M.map σ + N.map σ := by
  ext i j
  simp

theorem map_sub_ringEquiv (M N : Matrix (Fin 3) (Fin 3) K) :
    (M - N).map σ = M.map σ - N.map σ := by
  ext i j
  simp

theorem map_one_ringEquiv : (1 : Matrix (Fin 3) (Fin 3) K).map σ = 1 :=
  (σ.toRingHom.mapMatrix).map_one

theorem exists_hilbert90 (hcard : 3 < Fintype.card F) (hι : ∀ x, σ (ι x) = ι x) {ω : K}
    (hω : σ ω = -ω) (hω0 : ω ≠ 0) (h2 : (2 : K) ≠ 0) {A : Matrix (Fin 3) (Fin 3) K}
    (hAA : A * A.map σ = 1) : ∃ C : Matrix (Fin 3) (Fin 3) K, C.det ≠ 0 ∧ A * C.map σ = C := by
  classical
  set C₁ : Matrix (Fin 3) (Fin 3) K := 1 + A with hC₁
  set C₂ : Matrix (Fin 3) (Fin 3) K := ω • (1 - A) with hC₂
  have hfix : ∀ x : F, A * (C₁ + ι x • C₂).map σ = C₁ + ι x • C₂ := by
    intro x
    rw [map_add_ringEquiv, map_smul_ringEquiv, hC₁, hC₂, map_add_ringEquiv, map_one_ringEquiv,
      map_smul_ringEquiv, map_sub_ringEquiv, map_one_ringEquiv, hι, hω]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, hAA,
      smul_sub, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  let P : Polynomial K := Matrix.det ((Polynomial.X : Polynomial K) • C₂.map Polynomial.C +
    C₁.map Polynomial.C)
  have hdeg : P.natDegree ≤ 3 := by
    have := Polynomial.natDegree_det_X_add_C_le C₂ C₁
    simpa using this
  have hev : ∀ a : K, P.eval a = (C₁ + a • C₂).det := by
    intro a
    have := RingHom.map_det (Polynomial.evalRingHom a)
      ((Polynomial.X : Polynomial K) • C₂.map Polynomial.C + C₁.map Polynomial.C)
    have e : (Polynomial.evalRingHom a).mapMatrix
        ((Polynomial.X : Polynomial K) • C₂.map Polynomial.C + C₁.map Polynomial.C) =
        C₁ + a • C₂ := by
      ext i j
      simp
      ring
    rw [e] at this
    exact this
  by_contra hcon
  push Not at hcon
  have hall : ∀ x : F, P.eval (ι x) = 0 := by
    intro x
    rw [hev]
    by_contra hne
    exact hcon _ hne (hfix x)
  have hP0 : P = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P ι.injective hall (by omega)
  have h0 : P.eval ω⁻¹ = 0 := by rw [hP0]; simp
  rw [hev] at h0
  have hC : C₁ + ω⁻¹ • C₂ = (2 : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [hC₁, hC₂, smul_smul, inv_mul_cancel₀ hω0, one_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hC, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h0
  exact pow_ne_zero 3 h2 h0

end Hilbert

end CFSG.QuasithinUnique.Setup.Family
