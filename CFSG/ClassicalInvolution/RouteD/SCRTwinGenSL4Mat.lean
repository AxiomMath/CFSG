module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4

public section

namespace CFSG.ClassicalInvolution.RouteD.SCRSL4

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def upMat (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, M 0 0, M 0 1; 0, 1, M 1 0, M 1 1; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def loMat (N : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 1, 0, 0; N 0 0, N 0 1, 1, 0; N 1 0, N 1 1, 0, 1]

@[expose] def dMat (B B' : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![B 0 0, B 0 1, 0, 0; B 1 0, B 1 1, 0, 0; 0, 0, B' 0 0, B' 0 1; 0, 0, B' 1 0, B' 1 1]

theorem det_upMat (M : Matrix (Fin 2) (Fin 2) F) : (upMat M).det = 1 := by
  simp [upMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

theorem det_loMat (N : Matrix (Fin 2) (Fin 2) F) : (loMat N).det = 1 := by
  simp [loMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

@[expose] def up (M : Matrix (Fin 2) (Fin 2) F) : SL(4, F) := ⟨upMat M, det_upMat M⟩

@[expose] def lo (N : Matrix (Fin 2) (Fin 2) F) : SL(4, F) := ⟨loMat N, det_loMat N⟩

theorem up_mul (M M' : Matrix (Fin 2) (Fin 2) F) : up M * up M' = up (M + M') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [up, upMat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem lo_mul (N N' : Matrix (Fin 2) (Fin 2) F) : lo N * lo N' = lo (N + N') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lo, loMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem up_comm_dMat (M B B' : Matrix (Fin 2) (Fin 2) F) (h : M * B' = B * M) :
    upMat M * dMat B B' = dMat B B' * upMat M := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upMat, dMat, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first | linear_combination h00 | linear_combination h01 | linear_combination h10 |
    linear_combination h11

theorem lo_comm_dMat (N B B' : Matrix (Fin 2) (Fin 2) F) (h : N * B = B' * N) :
    loMat N * dMat B B' = dMat B B' * loMat N := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [loMat, dMat, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first | linear_combination h00 | linear_combination h01 | linear_combination h10 |
    linear_combination h11

theorem exists_up_decomp (h2 : (2 : F) ≠ 0) (B B' M : Matrix (Fin 2) (Fin 2) F)
    (hB : B * B = -1) (hB' : B' * B' = -1) :
    ∃ M₁ M₂ : Matrix (Fin 2) (Fin 2) F, M = M₁ + M₂ ∧ M₁ * B' = B * M₁ ∧
      M₂ * B' = (-B) * M₂ := by
  refine ⟨(2 : F)⁻¹ • (M - B * M * B'), (2 : F)⁻¹ • (M + B * M * B'), ?_, ?_, ?_⟩
  · rw [← smul_add]
    have : M - B * M * B' + (M + B * M * B') = (2 : F) • M := by
      rw [two_smul]; abel
    rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
  · have e1 : B * M * B' * B' = -(B * M) := by
      rw [mul_assoc, hB', mul_neg, mul_one]
    have e2 : B * (B * M * B') = -(M * B') := by
      rw [← mul_assoc, ← mul_assoc, hB, neg_mul, one_mul, neg_mul]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, e1, e2]
    congr 1
    abel
  · have e1 : B * M * B' * B' = -(B * M) := by
      rw [mul_assoc, hB', mul_neg, mul_one]
    have e2 : B * (B * M * B') = -(M * B') := by
      rw [← mul_assoc, ← mul_assoc, hB, neg_mul, one_mul, neg_mul]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_add, e1, e2]
    congr 1
    abel

theorem exists_lo_decomp (h2 : (2 : F) ≠ 0) (B B' N : Matrix (Fin 2) (Fin 2) F)
    (hB : B * B = -1) (hB' : B' * B' = -1) :
    ∃ N₁ N₂ : Matrix (Fin 2) (Fin 2) F, N = N₁ + N₂ ∧ N₁ * B = B' * N₁ ∧
      N₂ * (-B) = B' * N₂ := by
  refine ⟨(2 : F)⁻¹ • (N - B' * N * B), (2 : F)⁻¹ • (N + B' * N * B), ?_, ?_, ?_⟩
  · rw [← smul_add]
    have : N - B' * N * B + (N + B' * N * B) = (2 : F) • N := by
      rw [two_smul]; abel
    rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
  · have e1 : B' * N * B * B = -(B' * N) := by
      rw [mul_assoc, hB, mul_neg, mul_one]
    have e2 : B' * (B' * N * B) = -(N * B) := by
      rw [← mul_assoc, ← mul_assoc, hB', neg_mul, one_mul, neg_mul]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, e1, e2]
    congr 1
    abel
  · have e1 : B' * N * B * B = -(B' * N) := by
      rw [mul_assoc, hB, mul_neg, mul_one]
    have e2 : B' * (B' * N * B) = -(N * B) := by
      rw [← mul_assoc, ← mul_assoc, hB', neg_mul, one_mul, neg_mul]
    rw [Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    simp only [Matrix.add_mul, Matrix.mul_neg, Matrix.mul_add, e1, e2]
    abel

abbrev b0 (B : SL(2, F)) : SL(4, F) := blockSL F 4 2 0 (by norm_num) B

abbrev b2 (B : SL(2, F)) : SL(4, F) := blockSL F 4 2 2 (by norm_num) B

theorem coe_block_mul (B B' : SL(2, F)) :
    ((b0 B * b2 B' : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      dMat (B : Matrix (Fin 2) (Fin 2) F) B' := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL, coe_blockSL,
    CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4.blockMat_four_zero,
    CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4.blockMat_four_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem coe_mul_ut (g : SL(4, F)) (B B' : SL(2, F)) :
    ((g * (b0 B * b2 B') : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      (g : Matrix (Fin 4) (Fin 4) F) * dMat (B : Matrix (Fin 2) (Fin 2) F) B' := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_block_mul]

theorem coe_ut_mul (g : SL(4, F)) (B B' : SL(2, F)) :
    ((b0 B * b2 B' * g : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      dMat (B : Matrix (Fin 2) (Fin 2) F) B' * (g : Matrix (Fin 4) (Fin 4) F) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_block_mul]

theorem blockSL_zero_neg_mul (B B' : SL(2, F)) :
    (b0 (-1) * (b0 B * b2 B') : SL(4, F)) = b0 (-B) * b2 B' := by
  rw [← mul_assoc, ← map_mul, neg_one_mul]

theorem coe_b0_neg_one : ((b0 (-1) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [coe_blockSL, CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4.blockMat_four_zero]
  ext k l
  fin_cases k <;> fin_cases l <;> simp

theorem sup_eq_top (h2 : (2 : F) ≠ 0) (B B' : SL(2, F))
    (hB2 : (B : Matrix (Fin 2) (Fin 2) F) * B = -1)
    (hB'2 : (B' : Matrix (Fin 2) (Fin 2) F) * B' = -1) :
    Subgroup.centralizer ({b0 (-1)} : Set SL(4, F)) ⊔
      Subgroup.centralizer ({b0 B * b2 B'} : Set SL(4, F)) ⊔
      Subgroup.centralizer ({b0 (-1) * (b0 B * b2 B')} : Set SL(4, F)) = ⊤ := by
  set H := Subgroup.centralizer ({b0 (-1)} : Set SL(4, F)) ⊔
      Subgroup.centralizer ({b0 B * b2 B'} : Set SL(4, F)) ⊔
      Subgroup.centralizer ({b0 (-1) * (b0 B * b2 B')} : Set SL(4, F)) with hH
  have h1 : Subgroup.centralizer ({b0 (-1)} : Set SL(4, F)) ≤ H := le_trans le_sup_left le_sup_left
  have h2' : Subgroup.centralizer ({b0 B * b2 B'} : Set SL(4, F)) ≤ H :=
    le_trans le_sup_right le_sup_left
  have h3 : Subgroup.centralizer ({b0 (-1) * (b0 B * b2 B')} : Set SL(4, F)) ≤ H := le_sup_right
  have hup : ∀ M : Matrix (Fin 2) (Fin 2) F, up M ∈ H := by
    intro M
    obtain ⟨M₁, M₂, hM, hM₁, hM₂⟩ := exists_up_decomp h2 _ _ M hB2 hB'2
    have : up M = up M₁ * up M₂ := by rw [up_mul, hM]
    rw [this]
    refine H.mul_mem (h2' ?_) (h3 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      rw [coe_mul_ut, coe_ut_mul]
      exact up_comm_dMat M₁ _ _ hM₁
    · rw [Subgroup.mem_centralizer_singleton_iff, blockSL_zero_neg_mul]
      apply Subtype.ext
      rw [coe_mul_ut, coe_ut_mul, Matrix.SpecialLinearGroup.coe_neg]
      exact up_comm_dMat M₂ _ _ hM₂
  have hlo : ∀ N : Matrix (Fin 2) (Fin 2) F, lo N ∈ H := by
    intro N
    obtain ⟨N₁, N₂, hN, hN₁, hN₂⟩ := exists_lo_decomp h2 _ _ N hB2 hB'2
    have : lo N = lo N₁ * lo N₂ := by rw [lo_mul, hN]
    rw [this]
    refine H.mul_mem (h2' ?_) (h3 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      rw [coe_mul_ut, coe_ut_mul]
      exact lo_comm_dMat N₁ _ _ hN₁
    · rw [Subgroup.mem_centralizer_singleton_iff, blockSL_zero_neg_mul]
      apply Subtype.ext
      rw [coe_mul_ut, coe_ut_mul, Matrix.SpecialLinearGroup.coe_neg]
      exact lo_comm_dMat N₂ _ _ hN₂
  have hT : ∀ (i j : Fin 4) (hij : i ≠ j) (a : F),
      Matrix.SpecialLinearGroup.transvection hij a ∈ H := by
    intro i j hij a
    have hsame : (Matrix.SpecialLinearGroup.transvection hij a : SL(4, F)) *
        (b0 (-1) : SL(4, F)) = (b0 (-1) : SL(4, F)) *
        (Matrix.SpecialLinearGroup.transvection hij a : SL(4, F)) →
        Matrix.SpecialLinearGroup.transvection hij a ∈ H := by
      intro hc
      exact h1 (Subgroup.mem_centralizer_singleton_iff.mpr hc)
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · refine hsame (Subtype.ext ?_)
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_b0_neg_one,
        Matrix.SpecialLinearGroup.transvection_coe]
      ext k l
      fin_cases k <;> fin_cases l <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]
    · have e : Matrix.SpecialLinearGroup.transvection hij a = up (Matrix.single 0 0 a) := by
        apply Subtype.ext
        ext k l
        fin_cases k <;> fin_cases l <;>
          simp [Matrix.SpecialLinearGroup.transvection_coe, up, upMat]
      rw [e]; exact hup _
    · have e : Matrix.SpecialLinearGroup.transvection hij a = up (Matrix.single 0 1 a) := by
        apply Subtype.ext
        ext k l
        fin_cases k <;> fin_cases l <;>
          simp [Matrix.SpecialLinearGroup.transvection_coe, up, upMat]
      rw [e]; exact hup _
    · refine hsame (Subtype.ext ?_)
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_b0_neg_one,
        Matrix.SpecialLinearGroup.transvection_coe]
      ext k l
      fin_cases k <;> fin_cases l <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]
    · exact absurd rfl hij
    · have e : Matrix.SpecialLinearGroup.transvection hij a = up (Matrix.single 1 0 a) := by
        apply Subtype.ext
        ext k l
        fin_cases k <;> fin_cases l <;>
          simp [Matrix.SpecialLinearGroup.transvection_coe, up, upMat]
      rw [e]; exact hup _
    · have e : Matrix.SpecialLinearGroup.transvection hij a = up (Matrix.single 1 1 a) := by
        apply Subtype.ext
        ext k l
        fin_cases k <;> fin_cases l <;>
          simp [Matrix.SpecialLinearGroup.transvection_coe, up, upMat]
      rw [e]; exact hup _
    · have e : Matrix.SpecialLinearGroup.transvection hij a = lo (Matrix.single 0 0 a) := by
        apply Subtype.ext
        ext k l
        fin_cases k <;> fin_cases l <;>
          simp [Matrix.SpecialLinearGroup.transvection_coe, lo, loMat]
      rw [e]; exact hlo _
    · have e : Matrix.SpecialLinearGroup.transvection hij a = lo (Matrix.single 0 1 a) := by
        apply Subtype.ext
        ext k l
        fin_cases k <;> fin_cases l <;>
          simp [Matrix.SpecialLinearGroup.transvection_coe, lo, loMat]
      rw [e]; exact hlo _
    · exact absurd rfl hij
    · refine hsame (Subtype.ext ?_)
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_b0_neg_one,
        Matrix.SpecialLinearGroup.transvection_coe]
      ext k l
      fin_cases k <;> fin_cases l <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]
    · have e : Matrix.SpecialLinearGroup.transvection hij a = lo (Matrix.single 1 0 a) := by
        apply Subtype.ext
        ext k l
        fin_cases k <;> fin_cases l <;>
          simp [Matrix.SpecialLinearGroup.transvection_coe, lo, loMat]
      rw [e]; exact hlo _
    · have e : Matrix.SpecialLinearGroup.transvection hij a = lo (Matrix.single 1 1 a) := by
        apply Subtype.ext
        ext k l
        fin_cases k <;> fin_cases l <;>
          simp [Matrix.SpecialLinearGroup.transvection_coe, lo, loMat]
      rw [e]; exact hlo _
    · refine hsame (Subtype.ext ?_)
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_b0_neg_one,
        Matrix.SpecialLinearGroup.transvection_coe]
      ext k l
      fin_cases k <;> fin_cases l <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply]
    · exact absurd rfl hij
  rw [eq_top_iff]
  intro g _
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun g => g ∈ H) g ?_ hT
    (fun A B hA hB => H.mul_mem hA hB)
  intro i j hij c hc
  apply h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_b0_neg_one,
    Matrix.SpecialLinearGroup.diag2n_coe]
  ext k l
  fin_cases k <;> fin_cases l <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]

end CFSG.ClassicalInvolution.RouteD.SCRSL4
