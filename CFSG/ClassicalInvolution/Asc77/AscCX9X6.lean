module

public import CFSG.ClassicalInvolution.Asc77.AscCX9X1
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2L

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
  CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def d0GL : GL (Fin 4) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal ![-1, 1, 1, 1])
    (by simp [Fin.prod_univ_four])

@[expose] def c0GL : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal ![-1, 1]) (by simp)

theorem coe_d0GL : ((d0GL : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = diagonal ![-1, 1, 1, 1] :=
  rfl

theorem coe_c0GL : ((c0GL : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = diagonal ![-1, 1] := rfl

theorem coe_d0GL_inv :
    (((d0GL : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![-1, 1, 1, 1] := by
  rw [Matrix.coe_units_inv]
  refine Matrix.inv_eq_right_inv ?_
  show diagonal ![-1, 1, 1, 1] * diagonal ![-1, 1, 1, 1] = 1
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext k
  fin_cases k <;> simp

theorem coe_c0GL_inv :
    (((c0GL : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = diagonal ![-1, 1] := by
  rw [Matrix.coe_units_inv]
  refine Matrix.inv_eq_right_inv ?_
  show diagonal ![-1, 1] * diagonal ![-1, 1] = 1
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext k
  fin_cases k <;> simp

theorem d0_block0 (b : SL(2, F)) :
    slConjugation 4 F d0GL (blockSL F 4 2 0 (by norm_num) b) =
      blockSL F 4 2 0 (by norm_num) (slConjugation 2 F c0GL b) := by
  apply Subtype.ext
  rw [slConjugation_matrix, WeakCT.coe_blockSL, WeakCT.coe_blockSL, slConjugation_matrix,
    blockMat_four_zero, blockMat_four_zero]
  show diagonal ![-1, 1, 1, 1] * _ * (((d0GL : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) :
    Matrix (Fin 4) (Fin 4) F) = _
  rw [coe_d0GL_inv, coe_c0GL, coe_c0GL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem d0_block2 (b : SL(2, F)) :
    slConjugation 4 F d0GL (blockSL F 4 2 2 (by norm_num) b) = blockSL F 4 2 2 (by norm_num) b := by
  apply Subtype.ext
  rw [slConjugation_matrix, WeakCT.coe_blockSL, blockMat_four_two]
  show diagonal ![-1, 1, 1, 1] * _ * (((d0GL : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) :
    Matrix (Fin 4) (Fin 4) F) = _
  rw [coe_d0GL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem d0_spForm (m n : F) :
    diagonal ![-1, 1, 1, 1] * spForm m n * diagonal ![-1, 1, 1, 1] = spForm (-m) n := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spForm, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem d0_mem_spM {m n : F} {s : SL(4, F)} (hs : s ∈ spM (spForm m n)) :
    slConjugation 4 F d0GL s ∈ spM (spForm (-m) n) := by
  rw [mem_spM, slConjugation_matrix, coe_d0GL_inv]
  show diagonal ![-1, 1, 1, 1] * (s : Matrix (Fin 4) (Fin 4) F) * diagonal ![-1, 1, 1, 1] *
    spForm (-m) n * (diagonal ![-1, 1, 1, 1] * (s : Matrix (Fin 4) (Fin 4) F) *
      diagonal ![-1, 1, 1, 1])ᵀ = spForm (-m) n
  rw [Matrix.transpose_mul, Matrix.transpose_mul, diagonal_transpose, ← d0_spForm m n]
  have hs' := mem_spM.mp hs
  have hD : diagonal ![-1, 1, 1, 1] * diagonal ![-1, 1, 1, 1] = (1 : Matrix (Fin 4) (Fin 4) F) := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    fin_cases k <;> simp
  calc diagonal ![-1, 1, 1, 1] * (s : Matrix (Fin 4) (Fin 4) F) * diagonal ![-1, 1, 1, 1] *
        (diagonal ![-1, 1, 1, 1] * spForm m n * diagonal ![-1, 1, 1, 1]) *
          (diagonal ![-1, 1, 1, 1] * ((s : Matrix (Fin 4) (Fin 4) F)ᵀ *
            diagonal ![-1, 1, 1, 1]))
      = diagonal ![-1, 1, 1, 1] * ((s : Matrix (Fin 4) (Fin 4) F) *
          ((diagonal ![-1, 1, 1, 1] * diagonal ![-1, 1, 1, 1]) * spForm m n *
            (diagonal ![-1, 1, 1, 1] * diagonal ![-1, 1, 1, 1])) *
              (s : Matrix (Fin 4) (Fin 4) F)ᵀ) * diagonal ![-1, 1, 1, 1] := by
        simp only [Matrix.mul_assoc]
    _ = diagonal ![-1, 1, 1, 1] * spForm m n * diagonal ![-1, 1, 1, 1] := by
        rw [hD, Matrix.one_mul, Matrix.mul_one, hs']

theorem d0_d0 (s : SL(4, F)) : slConjugation 4 F d0GL (slConjugation 4 F d0GL s) = s := by
  rw [← MulAut.mul_apply, ← map_mul]
  have h : (d0GL : GL (Fin 4) F) * d0GL = 1 := by
    apply Units.ext
    rw [Units.val_mul, coe_d0GL, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
    congr 1
    funext k
    fin_cases k <;> simp
  rw [h, map_one, MulAut.one_apply]

theorem map_d0_spM (m n : F) :
    (spM (spForm m n)).map (slConjugation 4 F d0GL).toMonoidHom = spM (spForm (-m) n) := by
  refine le_antisymm (by rintro _ ⟨s, hs, rfl⟩; exact d0_mem_spM hs) fun s hs => ?_
  have hs' := d0_mem_spM hs
  rw [neg_neg] at hs'
  exact ⟨_, hs', d0_d0 s⟩

@[expose] def uT (t : F) : SL(2, F) :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_uT (t : F) : ((uT t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl

theorem upT_mul (s t : F) : uT s * uT t = uT (s + t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uT, coe_uT, coe_uT]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem upT_zero : uT (0 : F) = 1 := by
  apply Subtype.ext
  rw [coe_uT, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem upT_pow (t : F) (k : ℕ) : uT t ^ k = uT ((k : F) * t) := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, upT_zero]
  | succ k ih => rw [pow_succ, ih, upT_mul, Nat.cast_succ, add_mul, one_mul]

theorem orderOf_upT_one (p : ℕ) [Fact p.Prime] [CharP F p] : orderOf (uT (1 : F)) = p := by
  refine orderOf_eq_prime ?_ ?_
  · rw [upT_pow, CharP.cast_eq_zero, zero_mul, upT_zero]
  · intro h
    have := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [coe_uT] at this

theorem c0_upT (t : F) : slConjugation 2 F c0GL (uT t) = uT (-t) := by
  apply Subtype.ext
  rw [slConjugation_matrix, coe_c0GL_inv, coe_uT, coe_uT]
  show diagonal ![-1, 1] * _ * _ = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem upT_conj {t t' : F} (ht : t ≠ 0) {b : SL(2, F)}
    (h : b * uT t * b⁻¹ = uT t') :
    t' = (b : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t := by
  have h1 : b * uT t = uT t' * b := by rw [← h]; group
  have h2 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) h1
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uT] at h2
  have e11 := congrFun (congrFun h2 1) 1
  have e01 := congrFun (congrFun h2 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e11 e01
  have hdet := b.2
  rw [Matrix.det_fin_two] at hdet
  have hc : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    rcases e11 with h | h
    · exact h
    · exact absurd h ht
  rw [hc, mul_zero, sub_zero] at hdet
  linear_combination (-t') * hdet + (-(b : Matrix (Fin 2) (Fin 2) F) 0 0) * e01

theorem upT_not_conj (hsq : ¬ IsSquare (-1 : F)) {b : SL(2, F)} :
    b * uT 1 * b⁻¹ ≠ uT (-1) := by
  intro h
  apply hsq
  refine ⟨(b : Matrix (Fin 2) (Fin 2) F) 0 0, ?_⟩
  rw [upT_conj one_ne_zero h]
  ring

end CFSG.ClassicalInvolution.Asc77.CX.MF2L
