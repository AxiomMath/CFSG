module

public import CFSG.ClassicalInvolution.Asc77.AscB3C1

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock mat_longBlock)
open CFSG.ClassicalInvolution.Asc77.B3C (twShort twShort_apply Pel kron2 kronMat Pmat mat_Pel
  mat_kron2)
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def twMat (t : F) (M : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks
    !![(M 0 0 + M 1 1) * t, (M 0 0 - M 1 1) * t; (M 0 0 - M 1 1) * t, (M 0 0 + M 1 1) * t]
    !![(M 0 1 - M 1 0) * (t * t), (M 0 1 + M 1 0) * (t * t);
      (M 0 1 + M 1 0) * (t * t), (M 0 1 - M 1 0) * (t * t)]
    !![-M 0 1 + M 1 0, M 0 1 + M 1 0; M 0 1 + M 1 0, -M 0 1 + M 1 0]
    !![(M 0 0 + M 1 1) * t, (-M 0 0 + M 1 1) * t; (-M 0 0 + M 1 1) * t, (M 0 0 + M 1 1) * t]

@[expose] def PinvMat (t : F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks !![t, 0; t, 0] !![0, -t; 0, t] !![0, 1; 0, -1] !![1, 0; 1, 0]

theorem PinvMat_mul_Pmat (h2 : (2 : F) ≠ 0) : PinvMat (2⁻¹ : F) * Pmat F = 1 := by
  have ht : 2 * (2 : F)⁻¹ = 1 := mul_inv_cancel₀ h2
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [PinvMat, Pmat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.fromBlocks] <;> grind

theorem mat_twShort (h2 : (2 : F) ≠ 0) (M : SL(2, F)) :
    mat 2 F (twShort h2 M) = twMat (2⁻¹ : F) (M : Matrix (Fin 2) (Fin 2) F) := by
  have ht : 2 * (2 : F)⁻¹ = 1 := mul_inv_cancel₀ h2
  have h1 : Pel h2 * twShort h2 M = kron2 M * Pel h2 := by
    rw [twShort_apply]
    group
  have h1' := congrArg (mat 2 F) h1
  rw [map_mul, map_mul, mat_Pel, mat_kron2] at h1'
  have h3 : mat 2 F (twShort h2 M) =
      PinvMat (2⁻¹ : F) * (kronMat (M : Matrix (Fin 2) (Fin 2) F) * Pmat F) := by
    calc mat 2 F (twShort h2 M) = (PinvMat (2⁻¹ : F) * Pmat F) * mat 2 F (twShort h2 M) := by
          rw [PinvMat_mul_Pmat h2, Matrix.one_mul]
      _ = PinvMat (2⁻¹ : F) * (Pmat F * mat 2 F (twShort h2 M)) := by rw [Matrix.mul_assoc]
      _ = _ := by rw [h1']
  rw [h3]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [PinvMat, Pmat, kronMat, twMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.fromBlocks, Matrix.one_apply] <;> grind

theorem mat_longBlock_one (N : SL(2, F)) :
    mat 2 F (longBlock F 2 1 N) = blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
      (N : Matrix (Fin 2) (Fin 2) F) := mat_longBlock 1 N

@[expose] def conjD2 (t : F) (X : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  !![X 0 0, -(t * X 0 1); -(2 * X 1 0), X 1 1]

theorem conjD2_mul (t : F) (ht : 2 * t = 1) (X Y : Matrix (Fin 2) (Fin 2) F) :
    conjD2 t (X * Y) = conjD2 t X * conjD2 t Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjD2, Matrix.mul_apply, Fin.sum_univ_two] <;> grind

theorem conjD2_one (t : F) : conjD2 t (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjD2]

theorem det_conjD2 (t : F) (ht : 2 * t = 1) (X : Matrix (Fin 2) (Fin 2) F) :
    (conjD2 t X).det = X.det := by
  simp [conjD2, Matrix.det_fin_two]
  grind

@[expose] def conjD (t : F) (ht : 2 * t = 1) : SL(2, F) →* SL(2, F) where
  toFun X := ⟨conjD2 t (X : Matrix (Fin 2) (Fin 2) F), by
    rw [det_conjD2 t ht]
    exact X.2⟩
  map_one' := Subtype.ext (conjD2_one t)
  map_mul' X Y := Subtype.ext (conjD2_mul t ht X Y)

theorem coe_conjD (t : F) (ht : 2 * t = 1) (X : SL(2, F)) :
    ((conjD t ht X : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      conjD2 t (X : Matrix (Fin 2) (Fin 2) F) := rfl

theorem conjD_injective (t : F) (ht : 2 * t = 1) : Function.Injective (conjD t ht) := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  have h2 : (2 : F) ≠ 0 := by
    rintro h
    rw [h] at ht
    simp at ht
  intro X Y h
  have h' := congrArg (fun Z : SL(2, F) => (Z : Matrix (Fin 2) (Fin 2) F)) h
  simp only [coe_conjD] at h'
  have e01 := congrFun (congrFun h' 0) 1
  have e10 := congrFun (congrFun h' 1) 0
  have e00 := congrFun (congrFun h' 0) 0
  have e11 := congrFun (congrFun h' 1) 1
  simp [conjD2] at e01 e10 e00 e11
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01.resolve_right ht0
  · exact e10.resolve_right h2
  · exact e11

theorem conjD_surjective (t : F) (ht : 2 * t = 1) : Function.Surjective (conjD t ht) := by
  intro Y
  let X : Matrix (Fin 2) (Fin 2) F :=
    !![(Y : Matrix (Fin 2) (Fin 2) F) 0 0, -(2 * (Y : Matrix (Fin 2) (Fin 2) F) 0 1);
      -(t * (Y : Matrix (Fin 2) (Fin 2) F) 1 0), (Y : Matrix (Fin 2) (Fin 2) F) 1 1]
  have hdet : X.det = 1 := by
    have := Y.2
    rw [Matrix.det_fin_two] at this
    simp only [X, Matrix.det_fin_two_of]
    linear_combination this - ((Y : Matrix (Fin 2) (Fin 2) F) 0 1 *
      (Y : Matrix (Fin 2) (Fin 2) F) 1 0) * ht
  refine ⟨(⟨X, hdet⟩ : SL(2, F)), Subtype.ext ?_⟩
  show conjD2 t X = (Y : Matrix (Fin 2) (Fin 2) F)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjD2, X] <;> grind

end CFSG.ClassicalInvolution.PhanB3
