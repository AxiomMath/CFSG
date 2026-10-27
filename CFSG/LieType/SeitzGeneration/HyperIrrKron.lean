module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Data.Nat.Totient
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Tactic.FieldSimp

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

variable {F : Type*} [Field F] {p : ℕ}

@[expose] noncomputable def kr (A B : Matrix (Fin p) (Fin p) F) :
    Matrix (Fin (p * p)) (Fin (p * p)) F :=
  Matrix.reindexAlgEquiv F F finProdFinEquiv (Matrix.kroneckerMap (fun x y => x * y) A B)

theorem kr_apply (A B : Matrix (Fin p) (Fin p) F) (i j k l : Fin p) :
    kr A B (finProdFinEquiv (i, j)) (finProdFinEquiv (k, l)) = A i k * B j l := by
  simp [kr, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply]

theorem kr_mul (A A' B B' : Matrix (Fin p) (Fin p) F) :
    kr A B * kr A' B' = kr (A * A') (B * B') := by
  simp only [kr, ← map_mul, Matrix.mul_kronecker_mul]

theorem kr_one : kr (1 : Matrix (Fin p) (Fin p) F) 1 = 1 := by
  simp [kr]

theorem kr_add_left (A A' B : Matrix (Fin p) (Fin p) F) :
    kr (A + A') B = kr A B + kr A' B := by
  simp only [kr, Matrix.add_kronecker, map_add]

theorem kr_add_right (A B B' : Matrix (Fin p) (Fin p) F) :
    kr A (B + B') = kr A B + kr A B' := by
  simp only [kr, Matrix.kronecker_add, map_add]

theorem kr_smul_right (c : F) (A B : Matrix (Fin p) (Fin p) F) :
    kr A (c • B) = c • kr A B := by
  simp [kr, Matrix.kronecker_smul]

theorem kr_smul_left (c : F) (A B : Matrix (Fin p) (Fin p) F) :
    kr (c • A) B = c • kr A B := by
  simp [kr, Matrix.smul_kronecker]

theorem kr_zero_right (A : Matrix (Fin p) (Fin p) F) : kr A 0 = 0 := by
  simp [kr]

theorem kr_zero_left (B : Matrix (Fin p) (Fin p) F) : kr 0 B = 0 := by
  simp [kr]

theorem det_kr (A B : Matrix (Fin p) (Fin p) F) : (kr A B).det = A.det ^ p * B.det ^ p := by
  simp [kr, Matrix.coe_reindexAlgEquiv, Matrix.det_kronecker]

@[expose] def onesM : Matrix (Fin p) (Fin p) F := Matrix.of fun _ _ => 1

@[expose] def projF : Matrix (Fin p) (Fin p) F := ((p : F)⁻¹) • onesM

theorem onesM_mul_onesM : (onesM : Matrix (Fin p) (Fin p) F) * onesM = (p : F) • onesM := by
  ext i j
  simp [onesM, Matrix.mul_apply]

theorem projF_mul_projF (hpF : (p : F) ≠ 0) :
    (projF : Matrix (Fin p) (Fin p) F) * projF = projF := by
  simp only [projF, Matrix.smul_mul, Matrix.mul_smul, smul_smul, onesM_mul_onesM]
  rw [show (p : F)⁻¹ * ((p : F)⁻¹ * (p : F)) = (p : F)⁻¹ by field_simp]

@[expose] noncomputable def Mf (g : Matrix (Fin p) (Fin p) F) :
    Matrix (Fin (p * p)) (Fin (p * p)) F :=
  1 + kr projF (g - 1)

theorem Mf_one : Mf (1 : Matrix (Fin p) (Fin p) F) = 1 := by
  simp [Mf, kr_zero_right]

theorem Mf_mul (hpF : (p : F) ≠ 0) (g g' : Matrix (Fin p) (Fin p) F) :
    Mf g * Mf g' = Mf (g * g') := by
  have h1 : g * g' - 1 = (g - 1) + (g' - 1) + (g - 1) * (g' - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]; abel
  have h2 : kr projF (g - 1) * kr projF (g' - 1) = kr projF ((g - 1) * (g' - 1)) := by
    rw [kr_mul, projF_mul_projF hpF]
  simp only [Mf, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, h2, h1,
    kr_add_right]
  abel

theorem kr_one_mul_Mf_mul (u u' g : Matrix (Fin p) (Fin p) F) (huu : u * u' = 1) :
    kr 1 u * Mf g * kr 1 u' = Mf (u * g * u') := by
  have h1 : u * (g - 1) * u' = u * g * u' - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, huu]
  have h2 : kr 1 u * kr projF (g - 1) * kr 1 u' = kr projF (u * g * u' - 1) := by
    rw [kr_mul, kr_mul, ← h1]
    simp [Matrix.mul_assoc]
  have h3 : kr 1 u * kr 1 u' = 1 := by rw [kr_mul, huu, Matrix.one_mul, kr_one]
  simp only [Mf, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h3, h2]

end CFSG.LieType.SeitzGeneration
