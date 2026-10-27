module

public import CFSG.ClassicalInvolution.WeakCT.Standard
public import CFSG.ClassicalInvolution.WeakCT.AutExtend
public import CFSG.ClassicalInvolution.Models.LinearPairs.RootSL2

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace CHN

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def blk (F : Type) [Field F] (i : Fin 3) : SL(2, F) →* SL(4, F) :=
  blockSL F 4 2 i.val (by omega)

theorem coe_blk (i : Fin 3) (A : SL(2, F)) :
    ((blk F i A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      blockMat 4 i.val (A : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem blk_injective (i : Fin 3) : Function.Injective (blk F i) :=
  blockSL2_injective 3 i

theorem coe_blk_neg_one (i : Fin 3) :
    ((blk F i (-1) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = negBlock F 4 i.val := by
  show blockMat 4 i.val (((-1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) = _
  simp [negBlock]

theorem blk_neg_one_inv (i : Fin 3) : (blk F i (-1))⁻¹ = blk F i (-1) := by
  rw [← map_inv]
  congr 1
  simp

theorem blk2_neg_one_conj_blk1 (s : SL(2, F)) :
    blk F 2 (-1) * blk F 1 s * (blk F 2 (-1))⁻¹ = blk F 1 (diagConj2 1 (-1) s) := by
  rw [blk_neg_one_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blk_neg_one,
    coe_blk, coe_blk, coe_diagConj2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [negBlock_eq_diagonal, blockMat_apply, Matrix.mul_apply, Matrix.diagonal_apply,
      Fin.sum_univ_four]

theorem blk1_neg_one_conj_blk2 (s : SL(2, F)) :
    blk F 1 (-1) * blk F 2 s * (blk F 1 (-1))⁻¹ = blk F 2 (diagConj2 (-1) 1 s) := by
  rw [blk_neg_one_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blk_neg_one,
    coe_blk, coe_blk, coe_diagConj2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [negBlock_eq_diagonal, blockMat_apply, Matrix.mul_apply, Matrix.diagonal_apply,
      Fin.sum_univ_four]

theorem blk2_neg_one_comm_blk1_neg_one :
    blk F 2 (-1) * blk F 1 (-1) = blk F 1 (-1) * blk F 2 (-1) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blk_neg_one,
    coe_blk_neg_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [negBlock_eq_diagonal, Matrix.mul_apply, Matrix.diagonal_apply]

theorem diagConj2_one_neg_one_eq_self_iff (h2 : (2 : F) ≠ 0) (s : SL(2, F)) :
    diagConj2 1 (-1) s = s ↔ (s : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧
      (s : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) h
    simp only [coe_diagConj2] at h'
    have e01 := congrFun (congrFun h' 0) 1
    have e10 := congrFun (congrFun h' 1) 0
    simp [Matrix.mul_apply, Matrix.diagonal_apply] at e01 e10
    constructor
    · have : (2 : F) * (s : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination -e01
      exact (mul_eq_zero.mp this).resolve_left h2
    · have : (2 : F) * (s : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination -e10
      exact (mul_eq_zero.mp this).resolve_left h2
  · rintro ⟨h01, h10⟩
    apply Subtype.ext
    rw [coe_diagConj2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply, h01, h10]

theorem sl2_commute_of_diagonal (s t : SL(2, F)) (hs01 : (s : Matrix (Fin 2) (Fin 2) F) 0 1 = 0)
    (hs10 : (s : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (ht01 : (t : Matrix (Fin 2) (Fin 2) F) 0 1 = 0)
    (ht10 : (t : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) : s * t = t * s := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hs01, hs10, ht01, ht10, mul_comm]

theorem eq_one_of_blk_mem_center (i : Fin 3) (s : SL(2, F))
    (h : blk F i s ∈ Subgroup.center SL(4, F)) : s = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have key : ∀ k : Fin 4, ¬ (i.val ≤ k.val ∧ k.val < i.val + 2) → r = 1 := by
    intro k hk
    have := congrFun (congrFun hr k) k
    rw [coe_blk, blockMat_apply, dite_eq_right (fun h' => hk h'.1)] at this
    simpa using this
  have hr1 : r = 1 := by
    fin_cases i
    · exact key 3 (by simp)
    · exact key 0 (by simp)
    · exact key 0 (by simp)
  apply blk_injective i
  rw [map_one]
  apply Subtype.ext
  rw [← hr, hr1]
  simp

theorem blk0_mul_blk2_mem_center :
    blk F 0 (-1) * blk F 2 (-1) ∈ Subgroup.center SL(4, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp [Fintype.card_fin]; norm_num, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_blk_neg_one, coe_blk_neg_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [negBlock_eq_diagonal, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.scalar_apply]

theorem center_le_ker_of_neg_one {G : Type} [Group G] (hneg : ¬ IsSquare (-1 : F))
    (ψ : SL(4, F) →* G) (hψ : ψ (blk F 0 (-1) * blk F 2 (-1)) = 1) :
    Subgroup.center SL(4, F) ≤ ψ.ker := by
  intro x hx
  obtain ⟨r, hr4, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  simp only [Fintype.card_fin] at hr4
  have hr2 : r ^ 2 = 1 ∨ r ^ 2 = -1 := by
    have : (r ^ 2 - 1) * (r ^ 2 + 1) = 0 := by linear_combination hr4
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hr2' : r ^ 2 = 1 := by
    rcases hr2 with h | h
    · exact h
    · exact absurd ⟨r, by rw [← h]; ring⟩ hneg
  have hr1 : r = 1 ∨ r = -1 := by
    have : (r - 1) * (r + 1) = 0 := by linear_combination hr2'
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rw [MonoidHom.mem_ker]
  rcases hr1 with rfl | rfl
  · have : x = 1 := by
      apply Subtype.ext
      rw [← hrx]
      simp
    rw [this, map_one]
  · have : x = blk F 0 (-1) * blk F 2 (-1) := by
      apply Subtype.ext
      rw [← hrx, Matrix.SpecialLinearGroup.coe_mul, coe_blk_neg_one, coe_blk_neg_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [negBlock_eq_diagonal, Matrix.mul_apply, Matrix.diagonal_apply,
          Matrix.scalar_apply]
    rw [this, hψ]

@[expose] def permMat : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0]

theorem det_permMat : (permMat : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  simp [permMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

@[expose] def permSL : SL(4, F) := ⟨permMat, det_permMat⟩

theorem permSL_conj_blk2 (s : SL(2, F)) : permSL * blk F 2 s * permSL⁻¹ = blk F 1 s := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blk, coe_blk]
  show permMat * _ = _ * permMat
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [permMat, blockMat_apply, Matrix.mul_apply, Fin.sum_univ_four]

theorem blk_pair_one_two : ∃ W, LinearBlockStandardPair F W (blk F 1).range (blk F 2).range :=
  ⟨_, (weakCTSystem_standard (K := F) 3).pair 1 2 rfl⟩

theorem blk_sup_eq_top : (blk F 0).range ⊔ (blk F 1).range ⊔ (blk F 2).range = ⊤ := by
  rw [eq_top_iff, ← iSup_range_blockSL2 (K := F) 3]
  refine iSup_le fun i => ?_
  fin_cases i
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

end CHN

end CFSG.ClassicalInvolution.Asc77
