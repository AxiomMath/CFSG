module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreDedekind

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix

variable {F : Type} [Field F] {σ : F ≃+* F}

@[expose] def cycMat : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def cycMatInv : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem cycMat_mul_inv : (cycMat : Matrix (Fin 3) (Fin 3) F) * cycMatInv = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [cycMat, cycMatInv, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def dg (σ : F ≃+* F) (x : F) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.diagonal ![x, σ x, σ (σ x)]

theorem frobMat_map (h3 : orderOf σ = 3) (u : Fin 3 → F) :
    (frobMat σ u).map σ = frobMat σ u * cycMat := by
  ext i k
  fin_cases k <;> simp [frobMat, cycMat, Matrix.mul_apply, Fin.sum_univ_three, sigma_cube h3]

theorem cycMat_mul_map_dg (h3 : orderOf σ = 3) (x : F) :
    cycMat * (dg σ x).map σ = dg σ x * cycMat := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [cycMat, dg, Matrix.mul_apply, Fin.sum_univ_three, sigma_cube h3]

section Torus

variable (σ) in
@[expose] noncomputable def torusMat (u : Fin 3 → F) (x : F) : Matrix (Fin 3) (Fin 3) F :=
  frobMat σ u * dg σ x * (frobMat σ u)⁻¹

variable {u : Fin 3 → F} (hP : (frobMat σ u).det ≠ 0)
include hP

theorem torusMat_mul_frobMat (x : F) : torusMat σ u x * frobMat σ u = frobMat σ u * dg σ x := by
  rw [torusMat, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hP),
    Matrix.mul_one]

omit hP in
theorem frobMat_mulVec_single (u : Fin 3 → F) : frobMat σ u *ᵥ Pi.single 0 1 = u := by
  funext i
  simp [frobMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem torusMat_mulVec (x : F) : torusMat σ u x *ᵥ u = x • u := by
  have hu : frobMat σ u *ᵥ Pi.single 0 1 = u := frobMat_mulVec_single u
  have hd : dg σ x *ᵥ Pi.single 0 1 = x • Pi.single 0 1 := by
    funext i
    fin_cases i <;> simp [dg]
  calc torusMat σ u x *ᵥ u = torusMat σ u x *ᵥ (frobMat σ u *ᵥ Pi.single 0 1) := by rw [hu]
    _ = frobMat σ u *ᵥ (dg σ x *ᵥ Pi.single 0 1) := by
        rw [Matrix.mulVec_mulVec, torusMat_mul_frobMat hP, ← Matrix.mulVec_mulVec]
    _ = x • u := by rw [hd, Matrix.mulVec_smul, hu]

theorem isRatM_torusMat (h3 : orderOf σ = 3) (x : F) : IsRatM σ (torusMat σ u x) := by
  set P := frobMat σ u
  set M := (torusMat σ u x).map σ
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have h1 : M * P.map σ = P.map σ * (dg σ x).map σ := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, torusMat_mul_frobMat hP]
  rw [frobMat_map h3, ← Matrix.mul_assoc, Matrix.mul_assoc P, cycMat_mul_map_dg h3,
    ← Matrix.mul_assoc] at h1
  have h2 : M * P = P * dg σ x := by
    have := congrArg (· * cycMatInv) h1
    simpa only [Matrix.mul_assoc, cycMat_mul_inv, Matrix.mul_one] using this
  have h3' : M = torusMat σ u x := by
    calc M = M * P * P⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]
      _ = torusMat σ u x := by rw [h2]; rfl
  intro i j
  have := congrFun (congrFun h3' i) j
  simpa [M] using this

theorem det_torusMat (x : F) : (torusMat σ u x).det = x * σ x * σ (σ x) := by
  have hPu : IsUnit (frobMat σ u).det := isUnit_iff_ne_zero.mpr hP
  rw [torusMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, mul_comm,
    ← mul_assoc, Ring.inverse_mul_cancel _ hPu, one_mul, dg, Matrix.det_diagonal,
    Fin.prod_univ_three]
  simp

end Torus

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
