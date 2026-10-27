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
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4

open Matrix

variable {F : Type} [Field F]

@[expose] def E01 (t : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, t, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def E10 (t : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; t, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def E23 (t : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, t; 0, 0, 0, 1]

@[expose] def E32 (t : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, t, 1]

theorem diag_of_rel_zero (σ : F ≃+* F) (M : Matrix (Fin 4) (Fin 4) F) (hdet : M.det ≠ 0)
    (h01 : ∀ t : F, E01 t * M = M * E01 (σ t)) (h10 : ∀ t : F, E10 t * M = M * E10 (σ t))
    (h23 : ∀ t : F, E23 t * M = M * E23 (σ t)) (h32 : ∀ t : F, E32 t * M = M * E32 (σ t)) :
    σ = RingEquiv.refl F ∧ ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧
      M = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] := by
  have a01 := h01 1
  have a10 := h10 1
  have a23 := h23 1
  have a32 := h32 1
  rw [map_one] at a01 a10 a23 a32
  have m10 : M 1 0 = 0 := by
    have h := congrFun (congrFun a01 0) 0
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m11 : M 1 1 = M 0 0 := by
    have h := congrFun (congrFun a01 0) 1
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m12 : M 1 2 = 0 := by
    have h := congrFun (congrFun a01 0) 2
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m13 : M 1 3 = 0 := by
    have h := congrFun (congrFun a01 0) 3
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m20 : M 2 0 = 0 := by
    have h := congrFun (congrFun a01 2) 1
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m30 : M 3 0 = 0 := by
    have h := congrFun (congrFun a01 3) 1
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m01 : M 0 1 = 0 := by
    have h := congrFun (congrFun a10 1) 1
    simp [E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m02 : M 0 2 = 0 := by
    have h := congrFun (congrFun a10 1) 2
    simp [E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m03 : M 0 3 = 0 := by
    have h := congrFun (congrFun a10 1) 3
    simp [E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m21 : M 2 1 = 0 := by
    have h := congrFun (congrFun a10 2) 0
    simp [E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m31 : M 3 1 = 0 := by
    have h := congrFun (congrFun a10 3) 0
    simp [E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m32 : M 3 2 = 0 := by
    have h := congrFun (congrFun a23 2) 2
    simp [E23, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m33 : M 3 3 = M 2 2 := by
    have h := congrFun (congrFun a23 2) 3
    simp [E23, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m23 : M 2 3 = 0 := by
    have h := congrFun (congrFun a32 3) 3
    simp [E32, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have hM : M = !![M 0 0, 0, 0, 0; 0, M 0 0, 0, 0; 0, 0, M 2 2, 0; 0, 0, 0, M 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m10, m11, m12, m13, m20, m30, m01, m02, m03, m21, m31,
      m32, m33, m23]
  have ha : M 0 0 ≠ 0 := by
    intro h0
    apply hdet
    refine Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_
    fin_cases j <;> simp [h0, m01, m02, m03]
  have hb : M 2 2 ≠ 0 := by
    intro h0
    apply hdet
    refine Matrix.det_eq_zero_of_row_eq_zero 2 fun j => ?_
    fin_cases j <;> simp [h0, m20, m21, m23]
  have hσ : σ = RingEquiv.refl F := by
    ext t
    have h := congrFun (congrFun (h01 t) 0) 1
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    have h' : (t - σ t) * M 0 0 = 0 := by linear_combination h - t * m11
    have := (mul_eq_zero.mp h').resolve_right ha
    simpa using (sub_eq_zero.mp this).symm
  exact ⟨hσ, M 0 0, M 2 2, ha, hb, hM⟩

theorem antidiag_of_rel_one (σ : F ≃+* F) (M : Matrix (Fin 4) (Fin 4) F) (hdet : M.det ≠ 0)
    (h01 : ∀ t : F, E01 t * M = M * E10 (-σ t)) (h10 : ∀ t : F, E10 t * M = M * E01 (-σ t))
    (h23 : ∀ t : F, E23 t * M = M * E32 (-σ t)) (h32 : ∀ t : F, E32 t * M = M * E23 (-σ t)) :
    σ = RingEquiv.refl F ∧ ∃ m n : F, m ≠ 0 ∧ n ≠ 0 ∧
      M = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] := by
  have a01 := h01 1
  have a10 := h10 1
  have a23 := h23 1
  have a32 := h32 1
  rw [map_one] at a01 a10 a23 a32
  have m11 : M 1 1 = 0 := by
    have h := congrFun (congrFun a01 0) 1
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m12 : M 1 2 = 0 := by
    have h := congrFun (congrFun a01 0) 2
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m13 : M 1 3 = 0 := by
    have h := congrFun (congrFun a01 0) 3
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m21 : M 2 1 = 0 := by
    have h := congrFun (congrFun a01 2) 0
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m31 : M 3 1 = 0 := by
    have h := congrFun (congrFun a01 3) 0
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m10 : M 1 0 = -M 0 1 := by
    have h := congrFun (congrFun a01 0) 0
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m00 : M 0 0 = 0 := by
    have h := congrFun (congrFun a10 1) 0
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m02 : M 0 2 = 0 := by
    have h := congrFun (congrFun a10 1) 2
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m03 : M 0 3 = 0 := by
    have h := congrFun (congrFun a10 1) 3
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m20 : M 2 0 = 0 := by
    have h := congrFun (congrFun a10 2) 1
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m30 : M 3 0 = 0 := by
    have h := congrFun (congrFun a10 3) 1
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m33 : M 3 3 = 0 := by
    have h := congrFun (congrFun a23 2) 3
    simp [E23, E32, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m32 : M 3 2 = -M 2 3 := by
    have h := congrFun (congrFun a23 2) 2
    simp [E23, E32, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m22 : M 2 2 = 0 := by
    have h := congrFun (congrFun a32 3) 2
    simp [E23, E32, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have hM : M = !![0, M 0 1, 0, 0; -M 0 1, 0, 0, 0; 0, 0, 0, M 2 3; 0, 0, -M 2 3, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m00, m02, m03, m10, m11, m12, m13, m20, m21, m22, m30,
      m31, m32, m33]
  have hm : M 0 1 ≠ 0 := by
    intro h0
    apply hdet
    refine Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_
    fin_cases j <;> simp [h0, m00, m02, m03]
  have hn : M 2 3 ≠ 0 := by
    intro h0
    apply hdet
    refine Matrix.det_eq_zero_of_row_eq_zero 2 fun j => ?_
    fin_cases j <;> simp [h0, m20, m21, m22]
  have hσ : σ = RingEquiv.refl F := by
    ext t
    have h := congrFun (congrFun (h01 t) 0) 0
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    have h' : (σ t - t) * M 0 1 = 0 := by linear_combination h - t * m10
    have := (mul_eq_zero.mp h').resolve_right hm
    simpa using sub_eq_zero.mp this
  exact ⟨hσ, M 0 1, M 2 3, hm, hn, hM⟩

end CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
