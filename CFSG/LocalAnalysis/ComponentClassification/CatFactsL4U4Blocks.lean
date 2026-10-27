module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Conj4
public import CFSG.Assembly.Subnormal
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L4Core
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Blocks

open Matrix

variable {F : Type*} [Field F]

@[expose] def uA (a b : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, a, -b; 0, 1, b, a; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def uB (a b : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 1, 0, 0; a, -b, 1, 0; b, a, 0, 1]

@[expose] def hJ : Matrix (Fin 4) (Fin 4) F :=
  !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

@[expose] def wJ : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0]

@[expose] def formA : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]

theorem stdJ_mul_stdJ : (stdJ : Matrix (Fin 4) (Fin 4) F) * stdJ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stdJ, Matrix.mul_apply, Fin.sum_univ_four]

theorem uA_comm (a b : F) : uA a b * stdJ = stdJ * uA a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uA, stdJ, Matrix.mul_apply, Fin.sum_univ_four]

theorem uB_comm (a b : F) : uB a b * stdJ = stdJ * uB a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uB, stdJ, Matrix.mul_apply, Fin.sum_univ_four]

theorem hJ_comm : (hJ : Matrix (Fin 4) (Fin 4) F) * stdJ = stdJ * hJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hJ, stdJ, Matrix.mul_apply, Fin.sum_univ_four]

theorem wJ_comm : (wJ : Matrix (Fin 4) (Fin 4) F) * stdJ = stdJ * wJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wJ, stdJ, Matrix.mul_apply, Fin.sum_univ_four]

theorem det_uA (a b : F) : (uA a b).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [uA, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem det_uB (a b : F) : (uB a b).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [uB, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem det_hJ : (hJ : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [hJ, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem det_wJ : (wJ : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [wJ, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem uA_mul_uA (a b c d : F) : uA a b * uA c d = uA (a + c) (b + d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uA, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem uB_mul_uB (a b c d : F) : uB a b * uB c d = uB (a + c) (b + d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uB, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem uA_zero : (uA 0 0 : Matrix (Fin 4) (Fin 4) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uA]

theorem uB_zero : (uB 0 0 : Matrix (Fin 4) (Fin 4) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uB]

theorem hJ_mul_hJ : (hJ : Matrix (Fin 4) (Fin 4) F) * hJ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hJ, Matrix.mul_apply, Fin.sum_univ_four]

theorem wJ_mul_wJ : (wJ : Matrix (Fin 4) (Fin 4) F) * wJ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wJ, Matrix.mul_apply, Fin.sum_univ_four]

theorem commutator_hJ_uA (a b : F) :
    hJ * uA a b * (-hJ) * uA (-a) (-b) = uA (-2 * a) (-2 * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hJ, uA, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem commutator_hJ_uB (a b : F) :
    hJ * uB a b * (-hJ) * uB (-a) (-b) = uB (-2 * a) (-2 * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hJ, uB, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem commutator_hJ_wJ : (hJ : Matrix (Fin 4) (Fin 4) F) * wJ * (-hJ) * (-wJ) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hJ, wJ, Matrix.mul_apply, Fin.sum_univ_four]

local macro "blocks_norm" : tactic =>
  `(tactic| (
    simp only [uA, uB, stdJ, formA, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val,
      Matrix.neg_apply, Fin.isValue, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one]
    ring1))

theorem eq_of_comm_unipotents' {X : Matrix (Fin 4) (Fin 4) F} (h1 : X * uA 1 0 = uA 1 0 * X)
    (h2 : X * uA 0 1 = uA 0 1 * X) (h3 : X * uB 1 0 = uB 1 0 * X) :
    X = !![X 0 0, -X 1 0, 0, 0; X 1 0, X 0 0, 0, 0; 0, 0, X 0 0, -X 1 0; 0, 0, X 1 0, X 0 0] := by
  have E1 := fun i j => congrFun (congrFun h1 i) j
  have E2 := fun i j => congrFun (congrFun h2 i) j
  have E3 := fun i j => congrFun (congrFun h3 i) j
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · linear_combination (norm := blocks_norm) E1 1 2 + E2 0 2
  · linear_combination (norm := blocks_norm) E3 0 0
  · linear_combination (norm := blocks_norm) E3 0 1
  · simp
  · linear_combination (norm := blocks_norm) E1 1 3 + E2 0 3
  · linear_combination (norm := blocks_norm) E3 1 0
  · linear_combination (norm := blocks_norm) E3 1 1
  · linear_combination (norm := blocks_norm) -E1 0 0
  · linear_combination (norm := blocks_norm) -E1 0 1
  · linear_combination (norm := blocks_norm) -E1 0 2
  · linear_combination (norm := blocks_norm) -E1 0 3 + E1 1 2 + E2 0 2
  · linear_combination (norm := blocks_norm) -E1 1 0
  · linear_combination (norm := blocks_norm) -E1 1 1
  · linear_combination (norm := blocks_norm) -E1 1 2
  · linear_combination (norm := blocks_norm) E2 0 3

theorem eq_of_comm_unipotents {X : Matrix (Fin 4) (Fin 4) F} (h1 : X * uA 1 0 = uA 1 0 * X)
    (h2 : X * uA 0 1 = uA 0 1 * X) (h3 : X * uB 1 0 = uB 1 0 * X) :
    X = X 0 0 • 1 + X 1 0 • stdJ := by
  conv_lhs => rw [eq_of_comm_unipotents' h1 h2 h3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stdJ]

theorem transpose_eq_neg_of_unipotents {G : Matrix (Fin 4) (Fin 4) F}
    (h1 : uA 1 0 * G * (uA 1 0)ᵀ = G) (h2 : uA 0 1 * G * (uA 0 1)ᵀ = G)
    (h3 : uB 1 0 * G * (uB 1 0)ᵀ = G) : Gᵀ = -G := by
  have E1 := fun i j => congrFun (congrFun h1 i) j
  have E2 := fun i j => congrFun (congrFun h2 i) j
  have E3 := fun i j => congrFun (congrFun h3 i) j
  ext i j
  fin_cases i <;> fin_cases j
  · linear_combination (norm := blocks_norm) 2 * E3 0 2
  · linear_combination (norm := blocks_norm) E3 0 3 + E3 1 2
  · linear_combination (norm := blocks_norm) E1 0 0 - E1 0 2
  · linear_combination (norm := blocks_norm) E1 1 3 - E2 0 0
  · linear_combination (norm := blocks_norm) E3 0 3 + E3 1 2
  · linear_combination (norm := blocks_norm) 2 * E3 1 3
  · linear_combination (norm := blocks_norm)
      E1 0 1 - E1 0 3 + E1 1 0 - E1 1 2 - E1 1 3 + E2 0 0
  · linear_combination (norm := blocks_norm) E1 1 1 - E1 1 3
  · linear_combination (norm := blocks_norm) E1 0 0 - E1 0 2
  · linear_combination (norm := blocks_norm)
      E1 0 1 - E1 0 3 + E1 1 0 - E1 1 2 - E1 1 3 + E2 0 0
  · linear_combination (norm := blocks_norm) 2 * E1 0 2
  · linear_combination (norm := blocks_norm) E1 0 3 + E1 1 2
  · linear_combination (norm := blocks_norm) E1 1 3 - E2 0 0
  · linear_combination (norm := blocks_norm) E1 1 1 - E1 1 3
  · linear_combination (norm := blocks_norm) E1 0 3 + E1 1 2
  · linear_combination (norm := blocks_norm) 2 * E1 1 3

theorem eq_of_comm_stdJ {X : Matrix (Fin 4) (Fin 4) F} (h : X * stdJ = stdJ * X) :
    X = !![X 0 0, -X 1 0, X 0 2, -X 1 2; X 1 0, X 0 0, X 1 2, X 0 2;
      X 2 0, -X 3 0, X 2 2, -X 3 2; X 3 0, X 2 0, X 3 2, X 2 2] := by
  have E := fun i j => congrFun (congrFun h i) j
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · linear_combination (norm := blocks_norm) E 0 0
  · simp
  · linear_combination (norm := blocks_norm) E 0 2
  · simp
  · linear_combination (norm := blocks_norm) E 0 1
  · simp
  · linear_combination (norm := blocks_norm) E 0 3
  · simp
  · linear_combination (norm := blocks_norm) E 2 0
  · simp
  · linear_combination (norm := blocks_norm) E 2 2
  · simp
  · linear_combination (norm := blocks_norm) E 2 1
  · simp
  · linear_combination (norm := blocks_norm) E 2 3

theorem explicit_mul_formA_mul_transpose (p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ : F) :
    !![p₀, -p₁, p₂, -p₃; p₁, p₀, p₃, p₂; p₄, -p₅, p₆, -p₇; p₅, p₄, p₇, p₆] * formA *
        (!![p₀, -p₁, p₂, -p₃; p₁, p₀, p₃, p₂; p₄, -p₅, p₆, -p₇; p₅, p₄, p₇, p₆])ᵀ =
      ((p₀ * p₆ - p₁ * p₇ - p₂ * p₄ + p₃ * p₅) • 1 +
        (p₀ * p₇ + p₁ * p₆ - p₂ * p₅ - p₃ * p₄) • stdJ) * formA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [formA, stdJ, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring

theorem mul_formA_mul_transpose {X : Matrix (Fin 4) (Fin 4) F} (h : X * stdJ = stdJ * X) :
    ∃ α β : F, X * formA * Xᵀ = (α • 1 + β • stdJ) * formA := by
  rw [eq_of_comm_stdJ h]
  exact ⟨_, _, explicit_mul_formA_mul_transpose _ _ _ _ _ _ _ _⟩

theorem formA_transpose : (formA : Matrix (Fin 4) (Fin 4) F)ᵀ = -formA := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [formA]

theorem det_formA : (formA : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [formA, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem dotProduct_mulVec_self_eq_zero {n : Type*} [Fintype n] (h2 : (2 : F) ≠ 0)
    {M : Matrix n n F} (hM : Mᵀ = -M) (x : n → F) : x ⬝ᵥ (M *ᵥ x) = 0 := by
  have h : x ⬝ᵥ (M *ᵥ x) = -(x ⬝ᵥ (M *ᵥ x)) := by
    calc x ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ (Mᵀᵀ *ᵥ x) := by rw [Matrix.transpose_transpose]
      _ = (Mᵀ *ᵥ x) ⬝ᵥ x := by rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      _ = -(x ⬝ᵥ (M *ᵥ x)) := by
          rw [hM, Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]
  have : (2 : F) * (x ⬝ᵥ (M *ᵥ x)) = 0 := by linear_combination h
  exact (mul_eq_zero.1 this).resolve_left h2

theorem exists_transvection (h2 : (2 : F) ≠ 0) {A : Matrix (Fin 4) (Fin 4) F} (hA : Aᵀ = -A)
    (hAu : IsUnit A.det) :
    ∃ h : Matrix (Fin 4) (Fin 4) F, h.det = 1 ∧ h * A * hᵀ = A ∧ h * stdJ ≠ stdJ * h ∧
      h * stdJ ≠ -(stdJ * h) := by
  set v : Fin 4 → F := Pi.single 0 1 with hv
  set w : Fin 4 → F := A⁻¹ *ᵥ v with hw
  have hAi : (A⁻¹)ᵀ = -A⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hA]
    exact Matrix.inv_eq_right_inv (by rw [neg_mul_neg, Matrix.mul_nonsing_inv _ hAu])
  have hwv : w ⬝ᵥ v = 0 := by
    rw [hw, dotProduct_comm]
    exact dotProduct_mulVec_self_eq_zero h2 hAi v
  have hAw : A *ᵥ w = v := by rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAu,
    Matrix.one_mulVec]
  have hwA : w ᵥ* A = -v := by
    rw [← Matrix.mulVec_transpose, hA, Matrix.neg_mulVec, hAw]
  refine ⟨1 + vecMulVec v w, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow, hwv,
      add_zero]
  · have e1 : vecMulVec v w * A = vecMulVec v (-v) := by rw [Matrix.vecMulVec_mul, hwA]
    have e2 : A * vecMulVec w v = vecMulVec v v := by rw [Matrix.mul_vecMulVec, hAw]
    have e3 : vecMulVec v w * A * vecMulVec w v = 0 := by
      rw [e1, Matrix.vecMulVec_mul_vecMulVec, neg_dotProduct, dotProduct_comm v w, hwv,
        neg_zero, zero_smul]
      ext i j
      simp [Matrix.vecMulVec_apply]
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_vecMulVec]
    calc (1 + vecMulVec v w) * A * (1 + vecMulVec w v)
        = A + vecMulVec v w * A + A * vecMulVec w v + vecMulVec v w * A * vecMulVec w v := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
          abel
      _ = A := by
          rw [e3, e1, e2, add_zero]
          ext i j
          simp [Matrix.vecMulVec_apply]
  · intro hc
    have hw0 : ∀ j, w j = 0 := by
      intro j
      have := congrFun (congrFun hc 1) j
      simp [Matrix.mul_apply, Fin.sum_univ_four, stdJ, Matrix.vecMulVec_apply, hv,
        Matrix.one_apply] at this
      fin_cases j <;> simp_all
    have : v = 0 := by
      rw [← hAw]
      have : w = 0 := funext hw0
      rw [this, Matrix.mulVec_zero]
    have h1 := congrFun this 0
    simp [hv] at h1
  · intro hc
    have := congrFun (congrFun hc 3) 2
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.neg_apply,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.vecMulVec_apply, hv, stdJ, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val, Pi.single_apply] at this
    simp at this
    apply h2
    linear_combination this

end Blocks

end CFSG.ComponentClassification.CatFactsL4U4
