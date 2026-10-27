module

public import CFSG.ClassicalInvolution.WeakCT.UnitaryEightEmbed
public import CFSG.RankThree.PartTwo.CTU6.Nodes

public section

namespace CFSG.ClassicalInvolution.WeakCT.UnitaryEight

open Matrix CFSG.LieType.Universal.Unitary
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open CFSG.ClassicalInvolution.WeakCT (blk blk_zero_tv01 blk_zero_tv10 blk_one_tv01 blk_one_tv10
  hom_ext_sl2 blockSL coe_blockSL blockSL2)
open CFSG.RankThree.PartTwo.CTU6 (coe_tv embSL3 embSL3_tv01 embSL3_tv10 embSL3_tv12 embSL3_tv21
  rS0 rS1)
open CFSG.Timmesfeld (tv)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem coe_blockMat_one_add_single {m k o : ℕ} (h : o + k ≤ m) (i j : Fin k) (c : F) :
    blockMat m o (1 + single i j c) =
      (1 + single (⟨i.val + o, by omega⟩ : Fin m) ⟨j.val + o, by omega⟩ c :
        Matrix (Fin m) (Fin m) F) := by
  ext a b
  rw [blockMat_apply]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

theorem blockSL_tv {m k o : ℕ} (h : o + k ≤ m) {i j : Fin k} (hij : i ≠ j) (c : F) :
    blockSL F m k o h (tv i j c) =
      tv (⟨i.val + o, by omega⟩ : Fin m) ⟨j.val + o, by omega⟩ c := by
  have hij' : (⟨i.val + o, by omega⟩ : Fin m) ≠ ⟨j.val + o, by omega⟩ := by
    intro he
    exact hij (Fin.ext (by have := congrArg Fin.val he; simp only at this; omega))
  exact Subtype.ext (by rw [coe_blockSL, coe_tv hij, coe_tv hij']; exact
    coe_blockMat_one_add_single h i j c)

theorem blockSL2_three_tv01 (k : Fin 3) (c : F) :
    blockSL2 F 3 k (tv 0 1 c) = tv (⟨k.val, by omega⟩ : Fin 4) ⟨k.val + 1, by omega⟩ c := by
  have h := blockSL_tv (F := F) (m := 4) (k := 2) (o := k.val) (by omega)
    (i := 0) (j := 1) (by decide) c
  simp only [Fin.val_zero, Fin.val_one, zero_add] at h
  rw [show blockSL2 F 3 k = blockSL F 4 2 k.val (by omega) from rfl, h]
  congr 2
  omega

theorem blockSL2_three_tv10 (k : Fin 3) (c : F) :
    blockSL2 F 3 k (tv 1 0 c) = tv (⟨k.val + 1, by omega⟩ : Fin 4) ⟨k.val, by omega⟩ c := by
  have h := blockSL_tv (F := F) (m := 4) (k := 2) (o := k.val) (by omega)
    (i := 1) (j := 0) (by decide) c
  simp only [Fin.val_zero, Fin.val_one, zero_add] at h
  rw [show blockSL2 F 3 k = blockSL F 4 2 k.val (by omega) from rfl, h]
  congr 2
  omega

theorem blockSL_four_comp_blk_zero :
    (blockSL F 4 3 1 (by norm_num)).comp (blk F 0) = blockSL2 F 3 1 := by
  refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
  · rw [MonoidHom.comp_apply, blk_zero_tv01, blockSL_tv (by norm_num) (by decide),
      blockSL2_three_tv01]
    rfl
  · rw [MonoidHom.comp_apply, blk_zero_tv10, blockSL_tv (by norm_num) (by decide),
      blockSL2_three_tv10]
    rfl

theorem blockSL_four_comp_blk_one :
    (blockSL F 4 3 1 (by norm_num)).comp (blk F 1) = blockSL2 F 3 2 := by
  refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
  · rw [MonoidHom.comp_apply, blk_one_tv01, blockSL_tv (by norm_num) (by decide),
      blockSL2_three_tv01]
    rfl
  · rw [MonoidHom.comp_apply, blk_one_tv10, blockSL_tv (by norm_num) (by decide),
      blockSL2_three_tv10]
    rfl

variable (σ : F ≃+* F)

theorem lowBlk4_tv {i j : Fin 4} (h : i ≠ j) (c : F) :
    lowBlk4 σ (tv i j c) = 1 - single (Fin.rev j) (Fin.rev i) (σ c) := by
  have hinv : ((tv i j c)⁻¹ : SL(4, F)) = (1 + single i j (-c) : Matrix (Fin 4) (Fin 4) F) := by
    refine CFSG.RankThree.PartTwo.CTU6.coe_inv_eq_of_mul_eq_one ?_
    have h0 : single i j (-c) * single i j c = (0 : Matrix (Fin 4) (Fin 4) F) := by
      simp [Ne.symm h]
    rw [coe_tv h, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, h0, add_zero,
      add_assoc, ← single_add, add_neg_cancel, single_zero, add_zero]
  rw [lowBlk4, hinv, conjTr_add, conjTr_one, conjTr_single, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, antidiag_mul_self, antidiag_mul_single, single_mul_antidiag, map_neg,
    ← single_neg, ← sub_eq_add_neg]

variable (hσ : ∀ c, σ (σ c) = c)

theorem embSL4_tv01 (c : F) :
    embSL4 σ hσ (tv 0 1 c) =
      rootHom σ hσ (i := (0 : Fin 8)) (j := 1) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSL4, coe_rootHom, toAdd_ofAdd, embSL4Mat, lowBlk4_tv σ (by decide), coe_tv (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pairMat4_apply, rootMatrix, one_apply, Fin.rev]

theorem embSL4_tv10 (c : F) :
    embSL4 σ hσ (tv 1 0 c) =
      rootHom σ hσ (i := (1 : Fin 8)) (j := 0) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSL4, coe_rootHom, toAdd_ofAdd, embSL4Mat, lowBlk4_tv σ (by decide), coe_tv (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pairMat4_apply, rootMatrix, one_apply, Fin.rev]

theorem embSL4_tv12 (c : F) :
    embSL4 σ hσ (tv 1 2 c) =
      rootHom σ hσ (i := (1 : Fin 8)) (j := 2) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSL4, coe_rootHom, toAdd_ofAdd, embSL4Mat, lowBlk4_tv σ (by decide), coe_tv (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pairMat4_apply, rootMatrix, one_apply, Fin.rev]

theorem embSL4_tv21 (c : F) :
    embSL4 σ hσ (tv 2 1 c) =
      rootHom σ hσ (i := (2 : Fin 8)) (j := 1) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSL4, coe_rootHom, toAdd_ofAdd, embSL4Mat, lowBlk4_tv σ (by decide), coe_tv (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pairMat4_apply, rootMatrix, one_apply, Fin.rev]

theorem embSL4_tv23 (c : F) :
    embSL4 σ hσ (tv 2 3 c) =
      rootHom σ hσ (i := (2 : Fin 8)) (j := 3) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSL4, coe_rootHom, toAdd_ofAdd, embSL4Mat, lowBlk4_tv σ (by decide), coe_tv (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pairMat4_apply, rootMatrix, one_apply, Fin.rev]

theorem embSL4_tv32 (c : F) :
    embSL4 σ hσ (tv 3 2 c) =
      rootHom σ hσ (i := (3 : Fin 8)) (j := 2) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSL4, coe_rootHom, toAdd_ofAdd, embSL4Mat, lowBlk4_tv σ (by decide), coe_tv (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pairMat4_apply, rootMatrix, one_apply, Fin.rev]

theorem embSU6_rootHom01 (c : Multiplicative F) :
    embSU6 σ (rootHom σ hσ (i := (0 : Fin 6)) (j := 1) (by decide) (by decide) (by decide) c) =
      rootHom σ hσ (i := (1 : Fin 8)) (j := 2) (by decide) (by decide) (by decide) c := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSU6, coe_rootHom, coe_rootHom]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply, rootMatrix, one_apply, Fin.rev]

theorem embSU6_rootHom10 (c : Multiplicative F) :
    embSU6 σ (rootHom σ hσ (i := (1 : Fin 6)) (j := 0) (by decide) (by decide) (by decide) c) =
      rootHom σ hσ (i := (2 : Fin 8)) (j := 1) (by decide) (by decide) (by decide) c := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSU6, coe_rootHom, coe_rootHom]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply, rootMatrix, one_apply, Fin.rev]

theorem embSU6_rootHom12 (c : Multiplicative F) :
    embSU6 σ (rootHom σ hσ (i := (1 : Fin 6)) (j := 2) (by decide) (by decide) (by decide) c) =
      rootHom σ hσ (i := (2 : Fin 8)) (j := 3) (by decide) (by decide) (by decide) c := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSU6, coe_rootHom, coe_rootHom]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply, rootMatrix, one_apply, Fin.rev]

theorem embSU6_rootHom21 (c : Multiplicative F) :
    embSU6 σ (rootHom σ hσ (i := (2 : Fin 6)) (j := 1) (by decide) (by decide) (by decide) c) =
      rootHom σ hσ (i := (3 : Fin 8)) (j := 2) (by decide) (by decide) (by decide) c := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSU6, coe_rootHom, coe_rootHom]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply, rootMatrix, one_apply, Fin.rev]

theorem embSU6_comp_rS0 :
    (embSU6 σ).comp (rS0 σ hσ) = (embSL4 σ hσ).comp (blockSL2 F 3 1) := by
  refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, rS0, MonoidHom.comp_apply, blk_zero_tv01,
      embSL3_tv01, embSU6_rootHom01, blockSL2_three_tv01, ← embSL4_tv12]
    rfl
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, rS0, MonoidHom.comp_apply, blk_zero_tv10,
      embSL3_tv10, embSU6_rootHom10, blockSL2_three_tv10, ← embSL4_tv21]
    rfl

theorem embSU6_comp_rS1 :
    (embSU6 σ).comp (rS1 σ hσ) = (embSL4 σ hσ).comp (blockSL2 F 3 2) := by
  refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, rS1, MonoidHom.comp_apply, blk_one_tv01,
      embSL3_tv12, embSU6_rootHom12, blockSL2_three_tv01, ← embSL4_tv23]
    rfl
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, rS1, MonoidHom.comp_apply, blk_one_tv10,
      embSL3_tv21, embSU6_rootHom21, blockSL2_three_tv10, ← embSL4_tv32]
    rfl

end CFSG.ClassicalInvolution.WeakCT.UnitaryEight

end
