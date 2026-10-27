module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveOmeBlock
public import CFSG.ClassicalInvolution.WeakCT.Defs
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.ClassicalInvolution.Phan.Blocks

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix
open scoped commutatorElement

variable {F : Type} [Field F]

variable (F) in
@[expose] def leviQ : Subgroup (SpecialLinearGroup (Fin 4) F) where
  carrier := {M | (∀ j : Fin 3, (M : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) j.castSucc = 0) ∧
    (M : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) (Fin.last 3) = 1}
  one_mem' := ⟨fun j => by
      rw [Matrix.SpecialLinearGroup.coe_one, one_apply_ne (Fin.castSucc_lt_last j).ne'],
    by rw [Matrix.SpecialLinearGroup.coe_one, one_apply_eq]⟩
  mul_mem' := fun {M N} hM hN => ⟨fun j => by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      exact mul_apply_last_castSucc hM.1 hN.1 j,
    by rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply_last_last hM.1, hM.2, hN.2, one_mul]⟩
  inv_mem' := fun {M} hM => by
    have h := lastRow_of_mul_eq_one (M := (M : Matrix (Fin 4) (Fin 4) F))
      (N := ((M⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
      (by rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]) hM.1
    rw [hM.2, one_mul] at h
    exact h

theorem leviBlock_mul {M N : SpecialLinearGroup (Fin 4) F} (hN : N ∈ leviQ F) :
    ((M * N : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc
        Fin.castSucc =
      (M : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc *
        (N : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact submatrix_castSucc_mul_of_lastRow hN.1

theorem det_leviBlock {M : SpecialLinearGroup (Fin 4) F} (hM : M ∈ leviQ F) :
    ((M : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc).det = 1 := by
  have h := det_eq_of_lastRow hM.1
  rw [hM.2, one_mul, M.2] at h
  exact h.symm

theorem isColRadical_of_mem_leviQ {M : SpecialLinearGroup (Fin 4) F} (hM : M ∈ leviQ F)
    (h1 : (M : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc = 1) :
    IsColRadical (M : Matrix (Fin 4) (Fin 4) F) := by
  refine ⟨fun i j => ?_, hM.2⟩
  induction i using Fin.lastCases with
  | last => rw [hM.1 j, one_apply_ne (Fin.castSucc_lt_last j).ne']
  | cast i =>
    have h := congrFun (congrFun h1 i) j
    rw [submatrix_apply] at h
    rw [h, one_apply, one_apply]
    simp only [Fin.castSucc_inj]

theorem mem_leviQ_of_isColRadical {M : SpecialLinearGroup (Fin 4) F}
    (hM : IsColRadical (M : Matrix (Fin 4) (Fin 4) F)) : M ∈ leviQ F :=
  ⟨hM.lastRow, hM.2⟩

@[expose] def colRadSL (s : Fin 3 → F) : SpecialLinearGroup (Fin 4) F :=
  ⟨colRadMat s, det_colRadMat s⟩

theorem coe_colRadSL (s : Fin 3 → F) :
    ((colRadSL s : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = colRadMat s :=
  rfl

theorem IsColRadical.inv {M : SpecialLinearGroup (Fin 4) F}
    (hM : IsColRadical (M : Matrix (Fin 4) (Fin 4) F)) :
    IsColRadical ((M⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ∧
      colRadVec ((M⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        -colRadVec (M : Matrix (Fin 4) (Fin 4) F) := by
  have hQ : M⁻¹ ∈ leviQ F := inv_mem (mem_leviQ_of_isColRadical hM)
  have hb : ((M⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).submatrix
      Fin.castSucc Fin.castSucc = 1 := by
    have h := leviBlock_mul (M := M) hQ
    rw [mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, submatrix_castSucc_one] at h
    have h2 : (M : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc = 1 := by
      ext i j
      rw [submatrix_apply, hM.1, one_apply, one_apply]
      simp only [Fin.castSucc_inj]
    rw [h2, Matrix.one_mul] at h
    exact h.symm
  have hR := isColRadical_of_mem_leviQ hQ hb
  refine ⟨hR, ?_⟩
  have h := (hM.mul hR).2
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one] at h
  have h0 : colRadVec (1 : Matrix (Fin 4) (Fin 4) F) = 0 := by
    funext i
    rw [colRadVec, one_apply_ne (Fin.castSucc_lt_last i).ne, Pi.zero_apply]
  rw [h0] at h
  funext i
  have hi := congrFun h i
  simp only [Pi.zero_apply, Pi.add_apply] at hi
  simp only [Pi.neg_apply]
  linear_combination -hi

variable (F) in
@[expose] def leviEmbed : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 4) F :=
  CFSG.ClassicalInvolution.WeakCT.blockSL F 4 3 0 (by norm_num)

theorem leviEmbed_apply_castSucc (A : SpecialLinearGroup (Fin 3) F) (i j : Fin 3) :
    (leviEmbed F A : Matrix (Fin 4) (Fin 4) F) i.castSucc j.castSucc =
      (A : Matrix (Fin 3) (Fin 3) F) i j := by
  rw [leviEmbed, CFSG.ClassicalInvolution.WeakCT.coe_blockSL,
    CFSG.ClassicalInvolution.Phan.blockMat_apply]
  split_ifs with h
  · congr 1
  · exfalso
    apply h
    simp only [Fin.val_castSucc, zero_le, true_and, zero_add]
    exact ⟨i.isLt, j.isLt⟩

theorem leviEmbed_apply_last_left (A : SpecialLinearGroup (Fin 3) F) (j : Fin 4) :
    (leviEmbed F A : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) j =
      (1 : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) j := by
  rw [leviEmbed, CFSG.ClassicalInvolution.WeakCT.coe_blockSL,
    CFSG.ClassicalInvolution.Phan.blockMat_apply]
  split_ifs with h
  · exact absurd h.1.2 (by simp)
  · rfl

theorem leviEmbed_apply_last_right (A : SpecialLinearGroup (Fin 3) F) (i : Fin 4) :
    (leviEmbed F A : Matrix (Fin 4) (Fin 4) F) i (Fin.last 3) =
      (1 : Matrix (Fin 4) (Fin 4) F) i (Fin.last 3) := by
  rw [leviEmbed, CFSG.ClassicalInvolution.WeakCT.coe_blockSL,
    CFSG.ClassicalInvolution.Phan.blockMat_apply]
  split_ifs with h
  · exact absurd h.2.2 (by simp)
  · rfl

theorem leviEmbed_mem_leviQ (A : SpecialLinearGroup (Fin 3) F) : leviEmbed F A ∈ leviQ F :=
  ⟨fun j => by rw [leviEmbed_apply_last_left, one_apply_ne (Fin.castSucc_lt_last j).ne'],
    by rw [leviEmbed_apply_last_left, one_apply_eq]⟩

theorem leviBlock_leviEmbed (A : SpecialLinearGroup (Fin 3) F) :
    (leviEmbed F A : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc =
      (A : Matrix (Fin 3) (Fin 3) F) := by
  ext i j
  rw [submatrix_apply, leviEmbed_apply_castSucc]

theorem commutator_leviQ {ω : F} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ⁅leviQ F, leviQ F⁆ = leviQ F := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  intro M hM
  set A : SpecialLinearGroup (Fin 3) F :=
    ⟨(M : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc, det_leviBlock hM⟩
    with hAdef
  have hDA : leviEmbed F A ∈ ⁅leviQ F, leviQ F⁆ := by
    have hSL : A ∈ commutator (SpecialLinearGroup (Fin 3) F) := by
      rw [(CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) (n := 3)
        le_rfl).commutator_eq_top]
      exact Subgroup.mem_top A
    have h := Subgroup.mem_map_of_mem (leviEmbed F) hSL
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map] at h
    have hle : (leviEmbed F).range ≤ leviQ F := by
      rintro _ ⟨B, rfl⟩
      exact leviEmbed_mem_leviQ B
    exact Subgroup.commutator_mono hle hle h
  set R := M * (leviEmbed F A)⁻¹ with hRdef
  have hRQ : R ∈ leviQ F := mul_mem hM (inv_mem (leviEmbed_mem_leviQ A))
  have hRb : (R : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc = 1 := by
    rw [hRdef, ← map_inv, leviBlock_mul (leviEmbed_mem_leviQ _), leviBlock_leviEmbed]
    change (A : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = 1
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hRc := isColRadical_of_mem_leviQ hRQ hRb
  have hωdet : (ω • (1 : Matrix (Fin 3) (Fin 3) F)).det = 1 := by
    rw [Matrix.det_smul, det_one, mul_one, Fintype.card_fin, hω]
  set D := leviEmbed F ⟨ω • (1 : Matrix (Fin 3) (Fin 3) F), hωdet⟩ with hDdef
  have hDQ : D ∈ leviQ F := leviEmbed_mem_leviQ _
  have hDb : (D : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc =
      ω • (1 : Matrix (Fin 3) (Fin 3) F) := leviBlock_leviEmbed _
  set s' : Fin 3 → F := (ω - 1)⁻¹ • colRadVec (R : Matrix (Fin 4) (Fin 4) F) with hs'
  set R' := colRadSL s' with hR'def
  have hR'c : IsColRadical (R' : Matrix (Fin 4) (Fin 4) F) := isColRadical_colRadMat s'
  have hR'Q : R' ∈ leviQ F := mem_leviQ_of_isColRadical hR'c
  set E := D * R' * D⁻¹ with hEdef
  have hEQ : E ∈ leviQ F := mul_mem (mul_mem hDQ hR'Q) (inv_mem hDQ)
  have hEb : (E : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc = 1 := by
    have hR'b : (R' : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc = 1 := by
      ext i j
      rw [submatrix_apply, hR'c.1, one_apply, one_apply]
      simp only [Fin.castSucc_inj]
    rw [hEdef, leviBlock_mul (inv_mem hDQ), leviBlock_mul hR'Q, hR'b, Matrix.mul_one,
      ← leviBlock_mul (inv_mem hDQ), mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
      submatrix_castSucc_one]
  have hEc := isColRadical_of_mem_leviQ hEQ hEb
  have hEv : colRadVec (E : Matrix (Fin 4) (Fin 4) F) = ω • s' := by
    have h := colRadVec_eq_mulVec_of_mul_eq (x := (D : Matrix (Fin 4) (Fin 4) F)) hDQ.2 hR'c hEc
      (by rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hEdef,
        inv_mul_cancel_right])
    rw [h, hDb, Matrix.smul_mulVec, Matrix.one_mulVec, coe_colRadSL, colRadVec_colRadMat]
  have hC : ⁅D, R'⁆ = R := by
    rw [commutatorElement_def]
    have hCc := hEc.mul hR'c.inv.1
    apply Subtype.ext
    refine IsColRadical.ext (by rw [Matrix.SpecialLinearGroup.coe_mul]; exact hCc.1) hRc ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, hCc.2, hEv, hR'c.inv.2, coe_colRadSL,
      colRadVec_colRadMat, hs']
    have hω0 : ω - 1 ≠ 0 := sub_ne_zero.2 hω1
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    field_simp
    ring
  have hRmem : R ∈ ⁅leviQ F, leviQ F⁆ := hC ▸ Subgroup.commutator_mem_commutator hDQ hR'Q
  have hM' : M = R * leviEmbed F A := by rw [hRdef, inv_mul_cancel_right]
  rw [hM']
  exact mul_mem hRmem hDA

end CFSG.SeitzReduction.LinearPilot
