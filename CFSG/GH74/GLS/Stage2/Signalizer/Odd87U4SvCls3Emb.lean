module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvBlock
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section Emb

variable {K : Type} [Field K]

theorem eFirst_bar (φ : K →+* K) (M : Matrix (Fin 3) (Fin 3) K) :
    (eFirst M).map φ = eFirst (M.map φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eFirst]

theorem eLast_bar (φ : K →+* K) (M : Matrix (Fin 3) (Fin 3) K) :
    (eLast M).map φ = eLast (M.map φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eLast]

theorem eFirst_transpose (M : Matrix (Fin 3) (Fin 3) K) : (eFirst M)ᵀ = eFirst Mᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eFirst]

theorem eLast_transpose (M : Matrix (Fin 3) (Fin 3) K) : (eLast M)ᵀ = eLast Mᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eLast]

theorem eFirst_iso' (d0 d1 d2 d3 : K) {M : Matrix (Fin 3) (Fin 3) K}
    (hM : Mᵀ * Matrix.diagonal ![d1, d2, d3] * M = Matrix.diagonal ![d1, d2, d3]) :
    (eFirst M)ᵀ * Matrix.diagonal ![d0, d1, d2, d3] * eFirst M =
      Matrix.diagonal ![d0, d1, d2, d3] := by
  have e : ∀ i j : Fin 3, (Mᵀ * Matrix.diagonal ![d1, d2, d3] * M) i j =
      (Matrix.diagonal ![d1, d2, d3]) i j := fun i j => by rw [hM]
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  rw [eFirst_transpose, Matrix.mul_assoc]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eFirst, Matrix.mul_apply, Fin.sum_univ_four] <;>
    (first
      | linear_combination e00 | linear_combination e01 | linear_combination e02
      | linear_combination e10 | linear_combination e11 | linear_combination e12
      | linear_combination e20 | linear_combination e21 | linear_combination e22)

theorem eLast_iso' (d0 d1 d2 d3 : K) {M : Matrix (Fin 3) (Fin 3) K}
    (hM : Mᵀ * Matrix.diagonal ![d0, d1, d2] * M = Matrix.diagonal ![d0, d1, d2]) :
    (eLast M)ᵀ * Matrix.diagonal ![d0, d1, d2, d3] * eLast M =
      Matrix.diagonal ![d0, d1, d2, d3] := by
  have e : ∀ i j : Fin 3, (Mᵀ * Matrix.diagonal ![d0, d1, d2] * M) i j =
      (Matrix.diagonal ![d0, d1, d2]) i j := fun i j => by rw [hM]
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  rw [eLast_transpose, Matrix.mul_assoc]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eLast, Matrix.mul_apply, Fin.sum_univ_four] <;>
    (first
      | linear_combination e00 | linear_combination e01 | linear_combination e02
      | linear_combination e10 | linear_combination e11 | linear_combination e12
      | linear_combination e20 | linear_combination e21 | linear_combination e22)

theorem eFirst_iso (d : Fin 4 → K) {M : Matrix (Fin 3) (Fin 3) K}
    (hM : Mᵀ * Matrix.diagonal (fun i : Fin 3 => d i.succ) * M =
      Matrix.diagonal (fun i : Fin 3 => d i.succ)) :
    (eFirst M)ᵀ * Matrix.diagonal d * eFirst M = Matrix.diagonal d := by
  have hd : d = ![d 0, d 1, d 2, d 3] := by funext i; fin_cases i <;> rfl
  have he : (fun i : Fin 3 => d i.succ) = ![d 1, d 2, d 3] := by funext i; fin_cases i <;> rfl
  rw [he] at hM
  rw [hd]
  exact eFirst_iso' (d 0) (d 1) (d 2) (d 3) hM

theorem eLast_iso (d : Fin 4 → K) {M : Matrix (Fin 3) (Fin 3) K}
    (hM : Mᵀ * Matrix.diagonal (fun i : Fin 3 => d i.castSucc) * M =
      Matrix.diagonal (fun i : Fin 3 => d i.castSucc)) :
    (eLast M)ᵀ * Matrix.diagonal d * eLast M = Matrix.diagonal d := by
  have hd : d = ![d 0, d 1, d 2, d 3] := by funext i; fin_cases i <;> rfl
  have he : (fun i : Fin 3 => d i.castSucc) = ![d 0, d 1, d 2] := by funext i; fin_cases i <;> rfl
  rw [he] at hM
  rw [hd]
  exact eLast_iso' (d 0) (d 1) (d 2) (d 3) hM

end Emb

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
