module

public import CFSG.LieType.SpecialLinear.BinaryDescent.ExteriorTwist

public section

namespace CFSG.LieType.SpecialLinear

open Matrix
open ExteriorModel

variable {n i j : ℕ} {F : Type*} [Field F] [CharP F 2]

@[expose] noncomputable def slMatrix (A : Matrix.SpecialLinearGroup (Fin n) F) :
    Matrix (Fin n) (Fin n) F :=
  (A : Matrix (Fin n) (Fin n) F)

omit [CharP F 2] in
@[simp]
theorem slMatrix_one : slMatrix (1 : Matrix.SpecialLinearGroup (Fin n) F) = 1 := rfl

omit [CharP F 2] in
@[simp]
theorem slMatrix_mul (A B : Matrix.SpecialLinearGroup (Fin n) F) :
    slMatrix (A * B) = slMatrix A * slMatrix B := rfl

omit [CharP F 2] in
@[simp]
theorem slMatrix_transpose (A : Matrix.SpecialLinearGroup (Fin n) F) :
    slMatrix (SpecialLinearGroup.transpose A) = Matrix.transpose (slMatrix A) := rfl

@[expose] noncomputable def extTwistDual (n i j : ℕ) (F : Type*) [Field F] [CharP F 2] :
    Matrix.SpecialLinearGroup (Fin n) F →*
      Matrix (Set.powersetCard (Fin n) i) (Set.powersetCard (Fin n) i) F where
  toFun g := extTwist n i j F (SpecialLinearGroup.transpose (g⁻¹))
  map_one' := by
    have h : SpecialLinearGroup.transpose ((1 : Matrix.SpecialLinearGroup (Fin n) F)⁻¹) = 1 := by
      rw [inv_one]
      apply SpecialLinearGroup.ext
      intro p q
      have hmat :
          slMatrix (SpecialLinearGroup.transpose (1 : Matrix.SpecialLinearGroup (Fin n) F)) =
          slMatrix (1 : Matrix.SpecialLinearGroup (Fin n) F) := by
        rw [slMatrix_transpose, slMatrix_one, Matrix.transpose_one]
      simpa [slMatrix] using congrFun (congrFun hmat p) q
    rw [h, map_one]
  map_mul' g h := by
    have htrans : ∀ A B : Matrix.SpecialLinearGroup (Fin n) F,
        SpecialLinearGroup.transpose (A * B) =
          SpecialLinearGroup.transpose B * SpecialLinearGroup.transpose A := by
      intro A B
      apply SpecialLinearGroup.ext
      intro p q
      have hmat : slMatrix (SpecialLinearGroup.transpose (A * B)) =
          slMatrix (SpecialLinearGroup.transpose B * SpecialLinearGroup.transpose A) := by
        rw [slMatrix_transpose, slMatrix_mul, slMatrix_mul, slMatrix_transpose,
          slMatrix_transpose, Matrix.transpose_mul]
      simpa [slMatrix] using congrFun (congrFun hmat p) q
    rw [_root_.mul_inv_rev, htrans, map_mul]

@[simp]
theorem extTwistDual_apply (g : Matrix.SpecialLinearGroup (Fin n) F) :
    extTwistDual n i j F g = extTwist n i j F (SpecialLinearGroup.transpose (g⁻¹)) := rfl

end CFSG.LieType.SpecialLinear
