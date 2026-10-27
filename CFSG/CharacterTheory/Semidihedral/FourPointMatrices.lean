module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace CFSG.Semidihedral.FourPointMatrices

open Matrix

@[expose] def matrixA : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![0, 1; 1, 0]
@[expose] def matrixB : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 2; 0, 2]
@[expose] def matrixC : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 0; 0, 2]
@[expose] def matrixZ : Matrix (Fin 2) (Fin 2) (ZMod 3) := -1

theorem matrixA_square : matrixA * matrixA = 1 := by decide
theorem matrixB_square : matrixB * matrixB = 1 := by decide
theorem matrixC_square : matrixC * matrixC = 1 := by decide
theorem matrixZ_square : matrixZ * matrixZ = 1 := by decide

@[expose] def A : GeneralLinearGroup (Fin 2) (ZMod 3) :=
  ⟨matrixA, matrixA, matrixA_square, matrixA_square⟩
@[expose] def B : GeneralLinearGroup (Fin 2) (ZMod 3) :=
  ⟨matrixB, matrixB, matrixB_square, matrixB_square⟩
@[expose] def C : GeneralLinearGroup (Fin 2) (ZMod 3) :=
  ⟨matrixC, matrixC, matrixC_square, matrixC_square⟩
@[expose] def Z : GeneralLinearGroup (Fin 2) (ZMod 3) :=
  ⟨matrixZ, matrixZ, matrixZ_square, matrixZ_square⟩

theorem A_square : A ^ 2 = 1 := by
  apply Units.ext
  change matrixA ^ 2 = 1
  simpa only [pow_two] using matrixA_square

theorem B_square : B ^ 2 = 1 := by
  apply Units.ext
  change matrixB ^ 2 = 1
  simpa only [pow_two] using matrixB_square

theorem C_square : C ^ 2 = 1 := by
  apply Units.ext
  change matrixC ^ 2 = 1
  simpa only [pow_two] using matrixC_square

theorem Z_square : Z ^ 2 = 1 := by
  apply Units.ext
  change matrixZ ^ 2 = 1
  simpa only [pow_two] using matrixZ_square

theorem AB_cube : (A * B) ^ 3 = 1 := by
  apply Units.ext
  change (matrixA * matrixB) ^ 3 = 1
  decide

theorem BC_cube : (B * C) ^ 3 = 1 := by
  apply Units.ext
  change (matrixB * matrixC) ^ 3 = 1
  decide

theorem AC_square : (A * C) ^ 2 = Z := by
  apply Units.ext
  change (matrixA * matrixC) ^ 2 = matrixZ
  decide

theorem Z_mem_center : Z ∈ Subgroup.center (GeneralLinearGroup (Fin 2) (ZMod 3)) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Units.ext
  change (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (-1) =
    (-1) * (g : Matrix (Fin 2) (Fin 2) (ZMod 3))
  simp

theorem GL2_three_card : Nat.card (GeneralLinearGroup (Fin 2) (ZMod 3)) = 48 := by
  rw [Matrix.card_GL_field]
  norm_num [Fintype.card_fin]

@[expose] def parabolicMatrix (i : Fin 6) : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  match i.val with
  | 0 => 1
  | 1 => matrixA
  | 2 => matrixB
  | 3 => matrixA * matrixB
  | 4 => matrixB * matrixA
  | _ => matrixA * matrixB * matrixA

@[expose] def cosetMatrix (i : Fin 4) : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  match i.val with
  | 0 => 1
  | 1 => matrixC
  | 2 => matrixC * matrixB
  | _ => matrixC * matrixB * matrixA

@[expose] def normalMatrix (i : Fin 2 × Fin 6 × Fin 4) :
    Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  matrixZ ^ i.1.val * parabolicMatrix i.2.1 * cosetMatrix i.2.2

theorem normalMatrix_injective : Function.Injective normalMatrix := by decide

theorem invertibleMatrix_normalForm (M : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (hM : M.det ≠ 0) : ∃ i : Fin 2 × Fin 6 × Fin 4, normalMatrix i = M := by
  revert M
  decide

@[expose] def parabolicUnit (i : Fin 6) : GeneralLinearGroup (Fin 2) (ZMod 3) :=
  match i.val with
  | 0 => 1
  | 1 => A
  | 2 => B
  | 3 => A * B
  | 4 => B * A
  | _ => A * B * A

@[expose] def cosetUnit (i : Fin 4) : GeneralLinearGroup (Fin 2) (ZMod 3) :=
  match i.val with
  | 0 => 1
  | 1 => C
  | 2 => C * B
  | _ => C * B * A

@[expose] def normalUnit (i : Fin 2 × Fin 6 × Fin 4) : GeneralLinearGroup (Fin 2) (ZMod 3) :=
  Z ^ i.1.val * parabolicUnit i.2.1 * cosetUnit i.2.2

theorem normalUnit_matrix (i : Fin 2 × Fin 6 × Fin 4) :
    (normalUnit i : Matrix (Fin 2) (Fin 2) (ZMod 3)) = normalMatrix i := by
  rcases i with ⟨e, a, b⟩
  fin_cases e <;> fin_cases a <;> fin_cases b <;> rfl

theorem normalUnit_surjective : Function.Surjective normalUnit := by
  intro g
  obtain ⟨i, hi⟩ := invertibleMatrix_normalForm (g : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (GeneralLinearGroup.det_ne_zero g)
  exact ⟨i, Units.ext ((normalUnit_matrix i).trans hi)⟩

theorem normalUnit_injective : Function.Injective normalUnit := by
  intro i j h
  exact normalMatrix_injective (by simpa only [normalUnit_matrix] using congrArg Units.val h)

theorem normalUnit_mem_closure (i : Fin 2 × Fin 6 × Fin 4) :
    normalUnit i ∈ Subgroup.closure {A, B, C} := by
  let K := Subgroup.closure {A, B, C}
  have ha : A ∈ K := Subgroup.subset_closure (by simp)
  have hb : B ∈ K := Subgroup.subset_closure (by simp)
  have hc : C ∈ K := Subgroup.subset_closure (by simp)
  have hz : Z ∈ K := by
    rw [← AC_square]
    exact K.pow_mem (K.mul_mem ha hc) _
  have hp (j : Fin 6) : parabolicUnit j ∈ K := by
    fin_cases j <;> simp only [parabolicUnit]
    · exact K.one_mem
    · exact ha
    · exact hb
    · exact K.mul_mem ha hb
    · exact K.mul_mem hb ha
    · exact K.mul_mem (K.mul_mem ha hb) ha
  have hw (j : Fin 4) : cosetUnit j ∈ K := by
    fin_cases j <;> simp only [cosetUnit]
    · exact K.one_mem
    · exact hc
    · exact K.mul_mem hc hb
    · exact K.mul_mem (K.mul_mem hc hb) ha
  exact K.mul_mem (K.mul_mem (K.pow_mem hz _) (hp i.2.1)) (hw i.2.2)

theorem generators_closure : Subgroup.closure {A, B, C} = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨i, rfl⟩ := normalUnit_surjective g
  exact normalUnit_mem_closure i

theorem A_det : GeneralLinearGroup.det A = -1 := by
  apply Units.ext
  change matrixA.det = -1
  decide

theorem B_det : GeneralLinearGroup.det B = -1 := by
  apply Units.ext
  change matrixB.det = -1
  decide

theorem C_det : GeneralLinearGroup.det C = -1 := by
  apply Units.ext
  change matrixC.det = -1
  decide

theorem Z_matrix : (Z : Matrix (Fin 2) (Fin 2) (ZMod 3)) = -1 := rfl

theorem Z_order : orderOf Z = 2 := by
  apply orderOf_eq_prime Z_square
  intro h
  have hM : matrixZ = 1 := congrArg Units.val h
  have hn : matrixZ ≠ 1 := by decide
  exact hn hM

end CFSG.Semidihedral.FourPointMatrices
