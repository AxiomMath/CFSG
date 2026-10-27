module

public import CFSG.ClassicalInvolution.ModelFacts.MF15S1Mat

public section

namespace CFSG.ClassicalInvolution.ModelFacts.L6C

open Matrix Module CFSG.ClassicalInvolution.WeakCT
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (scalars_eq_center mem_scalars)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open CFSG.ClassicalInvolution.ModelFacts.MF15 (rotJ)
open scoped MatrixGroups

variable {F : Type} [Field F]

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) F

@[expose] def rot4 (F : Type) [Field F] : SL(4, F) := blockSL F 4 2 0 (by norm_num) rotJ

theorem blockMat_four_zero (A : Matrix (Fin 2) (Fin 2) F) :
    CFSG.ClassicalInvolution.Phan.blockMat 4 0 A =
      !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext a b
  rw [CFSG.ClassicalInvolution.Phan.blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem coe_rot4 : (rot4 F : 𝕄₄) = !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [rot4, WeakCT.coe_blockSL, blockMat_four_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotJ]

theorem coe_rot4_sq :
    ((rot4 F ^ 2 : SL(4, F)) : 𝕄₄) = !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_two, coe_rot4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem rot4_pow_four : rot4 F ^ 4 = 1 := by
  have h : rot4 F ^ 4 = (rot4 F ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_rot4_sq, pow_two, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem rot4_sq_not_central (h2 : (2 : F) ≠ 0) : rot4 F ^ 2 ∉ Subgroup.center SL(4, F) := by
  intro h
  rw [← scalars_eq_center] at h
  obtain ⟨c, -, hc⟩ := mem_scalars.mp h
  rw [coe_rot4_sq] at hc
  have h0 := congrFun (congrFun hc 0) 0
  have h2' := congrFun (congrFun hc 2) 2
  simp [Matrix.scalar_apply] at h0 h2'
  apply h2
  linear_combination h2' - h0

theorem diagonal_mul_rot4 {d : Fin 4 → F} (hd : d 0 = d 1) :
    Matrix.diagonal d * (rot4 F : 𝕄₄) = (rot4 F : 𝕄₄) * Matrix.diagonal d := by
  rw [coe_rot4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, hd]

theorem rot4_transpose_mul_diagonal (a c d : F) :
    (rot4 F : 𝕄₄)ᵀ * Matrix.diagonal ![a, a, c, d] * (rot4 F : 𝕄₄) =
      Matrix.diagonal ![a, a, c, d] := by
  rw [coe_rot4]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]

theorem rot4_transpose_mul_symp :
    (rot4 F : 𝕄₄)ᵀ * !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] * (rot4 F : 𝕄₄) =
      !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] := by
  rw [coe_rot4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem blockDiag_mul_rot4 (a b : F) (Y : Matrix (Fin 2) (Fin 2) F) :
    !![a, b, 0, 0; -b, a, 0, 0; 0, 0, Y 0 0, Y 0 1; 0, 0, Y 1 0, Y 1 1] * (rot4 F : 𝕄₄) =
      (rot4 F : 𝕄₄) *
        !![a, b, 0, 0; -b, a, 0, 0; 0, 0, Y 0 0, Y 0 1; 0, 0, Y 1 0, Y 1 1] := by
  rw [coe_rot4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]


@[expose] def colMat (v : Fin 4 → Fin 4 → F) : 𝕄₄ := Matrix.of fun r c => v c r

theorem mul_colMat (A : 𝕄₄) (v : Fin 4 → Fin 4 → F) :
    A * colMat v = colMat fun j => A *ᵥ v j := by
  ext r j
  simp [colMat, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem colMat_mul (v : Fin 4 → Fin 4 → F) (N : 𝕄₄) :
    colMat v * N = colMat fun j => ∑ k, N k j • v k := by
  ext r j
  simp [colMat, Matrix.mul_apply, Finset.sum_apply, mul_comm]

theorem isUnit_colMat {v : Fin 4 → Fin 4 → F} (hv : Submodule.span F (Set.range v) = ⊤) :
    IsUnit (colMat v) := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  intro y
  have hy : y ∈ LinearMap.range (colMat v).mulVecLin := by
    rw [Matrix.range_mulVecLin]
    have : Set.range (colMat v).col = Set.range v := by
      congr 1
    rw [this, hv]
    trivial
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, by simpa using hx⟩

noncomputable def colGL (v : Fin 4 → Fin 4 → F) (hv : Submodule.span F (Set.range v) = ⊤) :
    GL (Fin 4) F :=
  (isUnit_colMat hv).unit

theorem coe_colGL (v : Fin 4 → Fin 4 → F) (hv : Submodule.span F (Set.range v) = ⊤) :
    ((colGL v hv : GL (Fin 4) F) : 𝕄₄) = colMat v :=
  (isUnit_colMat hv).unit_spec

theorem slConj_fixed_of_comm {n : ℕ} (B P : GL (Fin n) F) (g : SL(n, F))
    (M : Matrix (Fin n) (Fin n) F)
    (hBP : (B : Matrix (Fin n) (Fin n) F) * P = (P : Matrix (Fin n) (Fin n) F) * M)
    (hMg : M * (g : Matrix (Fin n) (Fin n) F) = (g : Matrix (Fin n) (Fin n) F) * M) :
    slConjugation n F B (slConjugation n F P g) = slConjugation n F P g := by
  apply Subtype.ext
  rw [slConjugation_matrix, slConjugation_matrix]
  exact MF15.conj_fixed_matrix (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hBP hMg

theorem exists_sl_conj_block (P : GL (Fin 4) F) :
    ∃ k : SL(4, F), ∀ X : SL(2, F), k * blockSL F 4 2 0 (by norm_num) X * k⁻¹ =
      slConjugation 4 F P (blockSL F 4 2 0 (by norm_num) X) := by
  set d : F := (P : 𝕄₄).det with hd
  have hd0 : d ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det P).isUnit
    simpa [hd] using this
  let D : 𝕄₄ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, d⁻¹]
  have hK : ((P : 𝕄₄) * D).det = 1 := by
    rw [det_mul, ← hd]
    simp [D, det_succ_row_zero, Fin.sum_univ_succ, hd0]
  obtain ⟨k, hk⟩ : ∃ k : SL(4, F), (k : 𝕄₄) = (P : 𝕄₄) * D := ⟨⟨_, hK⟩, rfl⟩
  refine ⟨k, fun X => ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, slConjugation_matrix,
    hk]
  have hPP : ((P⁻¹ : GL (Fin 4) F) : 𝕄₄) * (P : 𝕄₄) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hDB : D * ((blockSL F 4 2 0 (by norm_num) X : SL(4, F)) : 𝕄₄) =
      ((blockSL F 4 2 0 (by norm_num) X : SL(4, F)) : 𝕄₄) * D := by
    rw [WeakCT.coe_blockSL, blockMat_four_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [D, Matrix.mul_apply, Fin.sum_univ_four]
  calc (P : 𝕄₄) * D * ((blockSL F 4 2 0 (by norm_num) X : SL(4, F)) : 𝕄₄)
      = (P : 𝕄₄) * (((blockSL F 4 2 0 (by norm_num) X : SL(4, F)) : 𝕄₄) * D) := by
        rw [Matrix.mul_assoc, hDB]
    _ = (P : 𝕄₄) * ((blockSL F 4 2 0 (by norm_num) X : SL(4, F)) : 𝕄₄) *
          (((P⁻¹ : GL (Fin 4) F) : 𝕄₄) * (P : 𝕄₄)) * D := by
        rw [hPP, Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

end CFSG.ClassicalInvolution.ModelFacts.L6C
