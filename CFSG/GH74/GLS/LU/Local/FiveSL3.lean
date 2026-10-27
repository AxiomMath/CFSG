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
public import Mathlib.RingTheory.PiTensorProduct
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

public section

open Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

section Transvections

variable {F : Type*} [Field F]

@[expose] def diag2nWord {i j : Fin 3} (hij : i ≠ j) (c : F) : SL(3, F) :=
  transvection hij c * transvection hij.symm (-c⁻¹) * transvection hij c *
    transvection hij (-1) * transvection hij.symm 1 * transvection hij (-1)

private theorem diag2n_eq_diag2nWord_01 {i j : Fin 3} (hij : i ≠ j) (hi : i = 0) (hj : j = 1)
    (c : F) (hc : c ≠ 0) : diag2n hij c hc = diag2nWord hij c := by
  subst hi hj
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [diag2nWord, diag2n_coe, transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply, mul_add, add_mul, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]

private theorem diag2n_eq_diag2nWord_02 {i j : Fin 3} (hij : i ≠ j) (hi : i = 0) (hj : j = 2)
    (c : F) (hc : c ≠ 0) : diag2n hij c hc = diag2nWord hij c := by
  subst hi hj
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [diag2nWord, diag2n_coe, transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply, mul_add, add_mul, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]

private theorem diag2n_eq_diag2nWord_10 {i j : Fin 3} (hij : i ≠ j) (hi : i = 1) (hj : j = 0)
    (c : F) (hc : c ≠ 0) : diag2n hij c hc = diag2nWord hij c := by
  subst hi hj
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [diag2nWord, diag2n_coe, transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply, mul_add, add_mul, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]

private theorem diag2n_eq_diag2nWord_12 {i j : Fin 3} (hij : i ≠ j) (hi : i = 1) (hj : j = 2)
    (c : F) (hc : c ≠ 0) : diag2n hij c hc = diag2nWord hij c := by
  subst hi hj
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [diag2nWord, diag2n_coe, transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply, mul_add, add_mul, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]

private theorem diag2n_eq_diag2nWord_20 {i j : Fin 3} (hij : i ≠ j) (hi : i = 2) (hj : j = 0)
    (c : F) (hc : c ≠ 0) : diag2n hij c hc = diag2nWord hij c := by
  subst hi hj
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [diag2nWord, diag2n_coe, transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply, mul_add, add_mul, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]

private theorem diag2n_eq_diag2nWord_21 {i j : Fin 3} (hij : i ≠ j) (hi : i = 2) (hj : j = 1)
    (c : F) (hc : c ≠ 0) : diag2n hij c hc = diag2nWord hij c := by
  subst hi hj
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [diag2nWord, diag2n_coe, transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply, mul_add, add_mul, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]

theorem diag2n_eq_diag2nWord {i j : Fin 3} (hij : i ≠ j) (c : F) (hc : c ≠ 0) :
    diag2n hij c hc = diag2nWord hij c := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact diag2n_eq_diag2nWord_01 hij rfl rfl c hc
  · exact diag2n_eq_diag2nWord_02 hij rfl rfl c hc
  · exact diag2n_eq_diag2nWord_10 hij rfl rfl c hc
  · exact absurd rfl hij
  · exact diag2n_eq_diag2nWord_12 hij rfl rfl c hc
  · exact diag2n_eq_diag2nWord_20 hij rfl rfl c hc
  · exact diag2n_eq_diag2nWord_21 hij rfl rfl c hc
  · exact absurd rfl hij

end Transvections

theorem sl3_five_le_of_transvections {Γ : Subgroup (GL (Fin 3) (ZMod 5))}
    (h : ∀ (i j : Fin 3) (hij : i ≠ j) (a : ZMod 5),
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij a) ∈ Γ)
    (s : SL(3, ZMod 5)) : Matrix.SpecialLinearGroup.toGL s ∈ Γ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction'
    (fun s => Matrix.SpecialLinearGroup.toGL s ∈ Γ) s ?_ h ?_
  · intro i j hij c hc
    show Matrix.SpecialLinearGroup.toGL (diag2n hij c hc) ∈ Γ
    rw [diag2n_eq_diag2nWord hij c hc]
    simp only [diag2nWord, map_mul]
    exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem (Γ.mul_mem (Γ.mul_mem (h _ _ _ _) (h _ _ _ _))
      (h _ _ _ _)) (h _ _ _ _)) (h _ _ _ _)) (h _ _ _ _)
  · intro A B hA hB
    simpa only [map_mul] using Γ.mul_mem hA hB

@[expose] def scalarGL (c : (ZMod 5)ˣ) : GL (Fin 3) (ZMod 5) :=
  Matrix.GeneralLinearGroup.scalar (Fin 3) c

@[simp] theorem coe_scalarGL (c : (ZMod 5)ˣ) :
    ((scalarGL c : GL (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) =
      Matrix.scalar (Fin 3) (c : ZMod 5) := rfl

@[simp] theorem scalarGL_one : scalarGL 1 = 1 := map_one _

theorem exists_lift_to_sl3 {M : Type} [Group M] (ρ : M →* GL (Fin 3) (ZMod 5))
    (hdet : ∀ m, Matrix.GeneralLinearGroup.det (ρ m) = 1) :
    ∃ φ : M →* SL(3, ZMod 5), ∀ m, Matrix.SpecialLinearGroup.toGL (φ m) = ρ m := by
  refine ⟨(Matrix.SpecialLinearGroup.toGLKerEquiv (n := Fin 3) (R := ZMod 5)).symm.toMonoidHom.comp
    (ρ.codRestrict _ (fun m => hdet m)), fun m => ?_⟩
  exact Units.ext rfl

end CFSG.GH74.GLS.LU.Local.Five
