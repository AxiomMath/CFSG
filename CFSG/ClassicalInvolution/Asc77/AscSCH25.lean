module

public import CFSG.ClassicalInvolution.Asc77.AscSCH04

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open Matrix
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def Rmat (x : K × K × K × K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, x.1, x.2.1; 0, 1, x.2.2.1, x.2.2.2; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def Vmat (y : K × K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, y.1, 0, 0; 0, 1, 0, 0; 0, 0, 1, y.2; 0, 0, 0, 1]

theorem Rmat_mul (x y : K × K × K × K) : Rmat x * Rmat y = Rmat (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rmat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem Rmat_zero : Rmat (0 : K × K × K × K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rmat]

theorem det_Rmat (x : K × K × K × K) : (Rmat x).det = 1 := by
  simp [Rmat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem Vmat_mul (x y : K × K) : Vmat x * Vmat y = Vmat (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Vmat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem Vmat_zero : Vmat (0 : K × K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Vmat]

theorem det_Vmat (x : K × K) : (Vmat x).det = 1 := by
  simp [Vmat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

@[expose] def rhoR : Multiplicative (K × K × K × K) →* SL(4, K) where
  toFun x := ⟨Rmat x.toAdd, det_Rmat _⟩
  map_one' := Subtype.ext (by simpa using Rmat_zero)
  map_mul' x y := Subtype.ext (Rmat_mul _ _).symm

@[expose] def rhoV : Multiplicative (K × K) →* SL(4, K) where
  toFun y := ⟨Vmat y.toAdd, det_Vmat _⟩
  map_one' := Subtype.ext (by simpa using Vmat_zero)
  map_mul' x y := Subtype.ext (Vmat_mul _ _).symm

theorem coe_rhoR (x : K × K × K × K) :
    ((rhoR (Multiplicative.ofAdd x) : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) = Rmat x := rfl

theorem coe_rhoV (y : K × K) :
    ((rhoV (Multiplicative.ofAdd y) : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) = Vmat y := rfl

theorem rhoR_injective :
    Function.Injective (rhoR : Multiplicative (K × K × K × K) →* SL(4, K)) := by
  intro x y h
  have h1 := congrArg (fun g : SL(4, K) => (g : Matrix (Fin 4) (Fin 4) K)) h
  have e02 := congrFun (congrFun h1 0) 2
  have e03 := congrFun (congrFun h1 0) 3
  have e12 := congrFun (congrFun h1 1) 2
  have e13 := congrFun (congrFun h1 1) 3
  simp only [rhoR, MonoidHom.coe_mk, Rmat] at e02 e03 e12 e13
  exact Multiplicative.toAdd.injective (Prod.ext e02 (Prod.ext e03 (Prod.ext e12 e13)))

theorem rhoV_injective : Function.Injective (rhoV : Multiplicative (K × K) →* SL(4, K)) := by
  intro x y h
  have h1 := congrArg (fun g : SL(4, K) => (g : Matrix (Fin 4) (Fin 4) K)) h
  have e01 := congrFun (congrFun h1 0) 1
  have e23 := congrFun (congrFun h1 2) 3
  simp only [rhoV, MonoidHom.coe_mk, Vmat] at e01 e23
  exact Multiplicative.toAdd.injective (Prod.ext e01 e23)

@[expose] def diagSL (t : Fin 4 → Kˣ) (ht : ∏ i, (t i : K) = 1) : SL(4, K) :=
  ⟨Matrix.diagonal fun i => (t i : K), by rw [Matrix.det_diagonal]; exact ht⟩

theorem coe_diagSL (t : Fin 4 → Kˣ) (ht : ∏ i, (t i : K) = 1) :
    ((diagSL t ht : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal fun i => (t i : K) :=
  rfl

theorem diagSL_conj_rhoR (t : Fin 4 → Kˣ) (ht : ∏ i, (t i : K) = 1) (x : K × K × K × K) :
    diagSL t ht * rhoR (Multiplicative.ofAdd x) * (diagSL t ht)⁻¹ =
      rhoR (Multiplicative.ofAdd ((t 0 : K) / t 2 * x.1, (t 0 : K) / t 3 * x.2.1,
        (t 1 : K) / t 2 * x.2.2.1, (t 1 : K) / t 3 * x.2.2.2)) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diagSL,
    coe_rhoR, coe_rhoR]
  have h0 := (t 0).ne_zero
  have h1 := (t 1).ne_zero
  have h2 := (t 2).ne_zero
  have h3 := (t 3).ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rmat, Matrix.mul_apply, Matrix.diagonal_apply] <;> field_simp

theorem diagSL_conj_rhoV (t : Fin 4 → Kˣ) (ht : ∏ i, (t i : K) = 1) (y : K × K) :
    diagSL t ht * rhoV (Multiplicative.ofAdd y) * (diagSL t ht)⁻¹ =
      rhoV (Multiplicative.ofAdd ((t 0 : K) / t 1 * y.1, (t 2 : K) / t 3 * y.2)) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diagSL,
    coe_rhoV, coe_rhoV]
  have h0 := (t 0).ne_zero
  have h1 := (t 1).ne_zero
  have h2 := (t 2).ne_zero
  have h3 := (t 3).ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Vmat, Matrix.mul_apply, Matrix.diagonal_apply] <;> field_simp

theorem rhoV_conj_rhoR (y : K × K) (x : K × K × K × K) :
    rhoV (Multiplicative.ofAdd y) * rhoR (Multiplicative.ofAdd x) *
        (rhoV (Multiplicative.ofAdd y))⁻¹ =
      rhoR (Multiplicative.ofAdd (x.1 + y.1 * x.2.2.1,
        x.2.1 + y.1 * x.2.2.2 - y.2 * x.1 - y.1 * y.2 * x.2.2.1, x.2.2.1,
        x.2.2.2 - y.2 * x.2.2.1)) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rhoV,
    coe_rhoR, coe_rhoR]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rmat, Vmat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

end CFSG.ClassicalInvolution.Asc77.SCH
