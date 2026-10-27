module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.LocalAnalysis.GLTheoremA.KD264LieA4

variable {K : Type} [Field K]

theorem det_conj_GL7 (A : GL (Fin 7) K) (x : Matrix.SpecialLinearGroup (Fin 7) K) :
    ((A : Matrix (Fin 7) (Fin 7) K) * (x : Matrix (Fin 7) (Fin 7) K) *
      ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)).det = 1 := by
  rw [Matrix.det_mul, Matrix.det_mul, x.2, mul_one, ← Matrix.det_mul, Units.mul_inv,
    Matrix.det_one]

@[expose] def conjSL7 (A : GL (Fin 7) K) :
    Matrix.SpecialLinearGroup (Fin 7) K ≃* Matrix.SpecialLinearGroup (Fin 7) K where
  toFun x := ⟨(A : Matrix (Fin 7) (Fin 7) K) * (x : Matrix (Fin 7) (Fin 7) K) *
    ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K), det_conj_GL7 A x⟩
  invFun x := ⟨((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
    (x : Matrix (Fin 7) (Fin 7) K) * (A : Matrix (Fin 7) (Fin 7) K), by
      rw [Matrix.det_mul, Matrix.det_mul, x.2, mul_one, ← Matrix.det_mul, Units.inv_mul,
        Matrix.det_one]⟩
  left_inv x := by
    apply Subtype.ext
    have hba : ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
        (A : Matrix (Fin 7) (Fin 7) K) = 1 := Units.inv_mul A
    show ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
      ((A : Matrix (Fin 7) (Fin 7) K) * (x : Matrix (Fin 7) (Fin 7) K) *
        ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) * (A : Matrix (Fin 7) (Fin 7) K) =
      (x : Matrix (Fin 7) (Fin 7) K)
    calc ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
          ((A : Matrix (Fin 7) (Fin 7) K) * (x : Matrix (Fin 7) (Fin 7) K) *
            ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) * (A : Matrix (Fin 7) (Fin 7) K)
        = (((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * (A : Matrix (Fin 7) (Fin 7) K)) *
          (x : Matrix (Fin 7) (Fin 7) K) *
          (((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * (A : Matrix (Fin 7) (Fin 7) K)) := by
          simp only [Matrix.mul_assoc]
      _ = (x : Matrix (Fin 7) (Fin 7) K) := by rw [Units.inv_mul A, Matrix.one_mul, Matrix.mul_one]
  right_inv x := by
    apply Subtype.ext
    show (A : Matrix (Fin 7) (Fin 7) K) *
      (((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * (x : Matrix (Fin 7) (Fin 7) K) *
        (A : Matrix (Fin 7) (Fin 7) K)) * ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) =
      (x : Matrix (Fin 7) (Fin 7) K)
    calc (A : Matrix (Fin 7) (Fin 7) K) *
          (((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * (x : Matrix (Fin 7) (Fin 7) K) *
            (A : Matrix (Fin 7) (Fin 7) K)) * ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)
        = ((A : Matrix (Fin 7) (Fin 7) K) * ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) *
          (x : Matrix (Fin 7) (Fin 7) K) *
          ((A : Matrix (Fin 7) (Fin 7) K) * ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) := by
          simp only [Matrix.mul_assoc]
      _ = (x : Matrix (Fin 7) (Fin 7) K) := by rw [Units.mul_inv A, Matrix.one_mul, Matrix.mul_one]
  map_mul' x y := by
    apply Subtype.ext
    show (A : Matrix (Fin 7) (Fin 7) K) * ((x : Matrix (Fin 7) (Fin 7) K) *
        (y : Matrix (Fin 7) (Fin 7) K)) * ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) =
      ((A : Matrix (Fin 7) (Fin 7) K) * (x : Matrix (Fin 7) (Fin 7) K) *
        ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) *
      ((A : Matrix (Fin 7) (Fin 7) K) * (y : Matrix (Fin 7) (Fin 7) K) *
        ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K))
    calc (A : Matrix (Fin 7) (Fin 7) K) * ((x : Matrix (Fin 7) (Fin 7) K) *
          (y : Matrix (Fin 7) (Fin 7) K)) * ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)
        = (A : Matrix (Fin 7) (Fin 7) K) * (x : Matrix (Fin 7) (Fin 7) K) *
          (((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * (A : Matrix (Fin 7) (Fin 7) K)) *
          (y : Matrix (Fin 7) (Fin 7) K) * ((A⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) := by
          rw [Units.inv_mul A]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

@[expose] def conjPSL7 [Finite K] (A : GL (Fin 7) K) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 7) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 7) K :=
  QuotientGroup.congr (Subgroup.center (Matrix.SpecialLinearGroup (Fin 7) K))
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 7) K)) (conjSL7 A)
    (map_center_equiv (conjSL7 A))

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
