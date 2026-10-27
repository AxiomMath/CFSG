module

public import CFSG.RankThree.PartTwo.CTU6.Embed

public section

namespace CFSG.ClassicalInvolution.WeakCT.UnitaryEight

open Matrix CFSG.LieType.Universal.Unitary
open CFSG.ClassicalInvolution.Phan (blockMat blockSel blockSel_apply blockSel_transpose_mul_self
  blockMat_mul blockMat_one det_blockMat conjTr_blockMat blockMat_apply blockMat_injective blockGL
  coe_blockGL)
open CFSG.RankThree.PartTwo.Sec4 (conjTr_conjTr_of_invol det_conjTr)
open CFSG.RankThree.PartTwo.CTU6 (antidiag_transpose conjTr_antidiag coe_inv_eq_of_mul_eq_one)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem antidiag_mul_blockSel_eight :
    (antidiag 8 : Matrix (Fin 8) (Fin 8) F) * blockSel F 8 6 1 =
      blockSel F 8 6 1 * (antidiag 6 : Matrix (Fin 6) (Fin 6) F) := by
  ext a j
  rw [mul_apply, mul_apply]
  fin_cases a <;> fin_cases j <;>
    simp [antidiag, blockSel_apply, Fin.sum_univ_succ, Fin.rev]

theorem blockMat_isometry_eight (σ : F ≃+* F) {A : Matrix (Fin 6) (Fin 6) F}
    (hA : conjTr σ A * antidiag 6 * A = antidiag 6) :
    conjTr σ (blockMat 8 1 A) * antidiag 8 * blockMat 8 1 A = antidiag 8 := by
  rw [conjTr_blockMat]
  have hL : (blockSel F 8 6 1)ᵀ * blockSel F 8 6 1 = 1 := blockSel_transpose_mul_self (by norm_num)
  have h1 := antidiag_mul_blockSel_eight (F := F)
  have h2 : (blockSel F 8 6 1)ᵀ * (antidiag 8 : Matrix (Fin 8) (Fin 8) F) =
      (antidiag 6 : Matrix (Fin 6) (Fin 6) F) * (blockSel F 8 6 1)ᵀ := by
    have := congrArg transpose h1
    rwa [transpose_mul, transpose_mul, antidiag_transpose, antidiag_transpose] at this
  unfold blockMat
  set L := blockSel F 8 6 1
  set J := (antidiag 8 : Matrix (Fin 8) (Fin 8) F)
  set J' := (antidiag 6 : Matrix (Fin 6) (Fin 6) F)
  set X := conjTr σ A - 1 with hX
  set Y := A - 1 with hY
  have key : J' * Y + X * J' + X * J' * Y = 0 := by
    have e : conjTr σ A = X + 1 := by rw [hX, sub_add_cancel]
    have e' : A = Y + 1 := by rw [hY, sub_add_cancel]
    rw [e, e'] at hA
    have : (X + 1) * J' * (Y + 1) - J' = J' * Y + X * J' + X * J' * Y := by noncomm_ring
    rw [← this, hA, sub_self]
  have e1 : J * (L * Y * Lᵀ) = L * (J' * Y) * Lᵀ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc L J' Y]
  have e2 : L * X * Lᵀ * J = L * (X * J') * Lᵀ := by
    rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, Matrix.mul_assoc L X J']
  have e3 : L * X * Lᵀ * J * (L * Y * Lᵀ) = L * (X * J' * Y) * Lᵀ := by
    rw [e2]
    calc L * (X * J') * Lᵀ * (L * Y * Lᵀ) = L * (X * J') * (Lᵀ * L) * Y * Lᵀ := by
          simp only [Matrix.mul_assoc]
      _ = L * (X * J' * Y) * Lᵀ := by rw [hL, Matrix.mul_one, Matrix.mul_assoc L (X * J') Y]
  calc (1 + L * X * Lᵀ) * J * (1 + L * Y * Lᵀ)
      = J + J * (L * Y * Lᵀ) + L * X * Lᵀ * J + L * X * Lᵀ * J * (L * Y * Lᵀ) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
        abel
    _ = J + L * (J' * Y + X * J' + X * J' * Y) * Lᵀ := by
        rw [e3, e1, e2, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
        abel
    _ = J := by rw [key, Matrix.mul_zero, Matrix.zero_mul, add_zero]

@[expose] noncomputable def embSU6 (σ : F ≃+* F) : SU σ 6 →* SU σ 8 :=
  ((blockGL 8 1 (by norm_num)).comp (SU σ 6).subtype).codRestrict (SU σ 8) fun g =>
    ⟨by rw [MonoidHom.comp_apply, coe_blockGL, det_blockMat (by norm_num)]; exact g.2.1,
      by rw [MonoidHom.comp_apply, coe_blockGL]; exact blockMat_isometry_eight σ g.2.2⟩

theorem coe_embSU6 (σ : F ≃+* F) (g : SU σ 6) :
    (((embSU6 σ g : SU σ 8) : GL (Fin 8) F) : Matrix (Fin 8) (Fin 8) F) =
      blockMat 8 1 ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) :=
  rfl

theorem embSU6_injective (σ : F ≃+* F) : Function.Injective (embSU6 σ) := by
  intro g g' h
  have h' := congrArg (fun x : SU σ 8 => ((x : GL (Fin 8) F) : Matrix (Fin 8) (Fin 8) F)) h
  simp only [coe_embSU6] at h'
  exact Subtype.ext (Units.ext (blockMat_injective (by norm_num) h'))

@[expose] def pairMat4 (M N : Matrix (Fin 4) (Fin 4) F) : Matrix (Fin 8) (Fin 8) F :=
  reindex finSumFinEquiv finSumFinEquiv (fromBlocks M 0 0 N)

theorem pairMat4_mul (M N M' N' : Matrix (Fin 4) (Fin 4) F) :
    pairMat4 M N * pairMat4 M' N' = pairMat4 (M * M') (N * N') := by
  simp only [pairMat4, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem pairMat4_one : pairMat4 (1 : Matrix (Fin 4) (Fin 4) F) 1 = 1 := by
  simp [pairMat4, fromBlocks_one]

theorem det_pairMat4 (M N : Matrix (Fin 4) (Fin 4) F) : (pairMat4 M N).det = M.det * N.det := by
  rw [pairMat4, det_reindex_self, det_fromBlocks_zero₂₁]

theorem conjTr_pairMat4 (σ : F ≃+* F) (M N : Matrix (Fin 4) (Fin 4) F) :
    conjTr σ (pairMat4 M N) = pairMat4 (conjTr σ M) (conjTr σ N) := by
  rw [conjTr, conjTr, conjTr, pairMat4, pairMat4, reindex_apply, reindex_apply, ← submatrix_map,
    transpose_submatrix, fromBlocks_map, fromBlocks_transpose, Matrix.map_zero _ (map_zero σ),
    transpose_zero]

theorem pairMat4_apply (M N : Matrix (Fin 4) (Fin 4) F) (a b : Fin 8) :
    pairMat4 M N a b =
      if h : a.val < 4 ∧ b.val < 4 then M ⟨a.val, h.1⟩ ⟨b.val, h.2⟩
      else if h' : 4 ≤ a.val ∧ 4 ≤ b.val then
        N ⟨a.val - 4, by omega⟩ ⟨b.val - 4, by omega⟩
      else 0 := by
  fin_cases a <;> fin_cases b <;> rfl

theorem antidiag_eight_eq :
    (antidiag 8 : Matrix (Fin 8) (Fin 8) F) =
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks 0 (antidiag 4) (antidiag 4) 0) := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem pairMat4_mul_antidiag_mul (M N M' N' : Matrix (Fin 4) (Fin 4) F) :
    pairMat4 M N * (antidiag 8 : Matrix (Fin 8) (Fin 8) F) * pairMat4 M' N' =
      reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks 0 (M * antidiag 4 * N') (N * antidiag 4 * M') 0) := by
  rw [antidiag_eight_eq]
  simp only [pairMat4, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  simp

variable (σ : F ≃+* F)

@[expose] def lowBlk4 (M : SL(4, F)) : Matrix (Fin 4) (Fin 4) F :=
  (antidiag 4 : Matrix (Fin 4) (Fin 4) F) * conjTr σ ((M⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
    antidiag 4

@[expose] def embSL4Mat (M : SL(4, F)) : Matrix (Fin 8) (Fin 8) F :=
  pairMat4 (M : Matrix (Fin 4) (Fin 4) F) (lowBlk4 σ M)

theorem lowBlk4_mul (M M' : SL(4, F)) : lowBlk4 σ (M * M') = lowBlk4 σ M * lowBlk4 σ M' := by
  have hJ := antidiag_mul_self (F := F) 4
  simp only [lowBlk4, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, conjTr_mul]
  set J := (antidiag 4 : Matrix (Fin 4) (Fin 4) F)
  set C := conjTr σ ((M⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
  set C' := conjTr σ ((M'⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
  calc J * (C * C') * J = J * C * (J * J) * C' * J := by
        rw [hJ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = J * C * J * (J * C' * J) := by simp only [Matrix.mul_assoc]

theorem lowBlk4_one : lowBlk4 σ (1 : SL(4, F)) = 1 := by
  rw [lowBlk4, inv_one, Matrix.SpecialLinearGroup.coe_one, conjTr_one, Matrix.mul_one,
    antidiag_mul_self]

theorem det_lowBlk4 (M : SL(4, F)) : (lowBlk4 σ M).det = 1 := by
  have hJ := congrArg Matrix.det (antidiag_mul_self (F := F) 4)
  rw [det_mul, det_one] at hJ
  rw [lowBlk4, det_mul, det_mul, det_conjTr, (M⁻¹).2, map_one, mul_one, hJ]

theorem det_embSL4Mat (M : SL(4, F)) : (embSL4Mat σ M).det = 1 := by
  rw [embSL4Mat, det_pairMat4, M.2, det_lowBlk4, one_mul]

theorem embSL4Mat_mul (M M' : SL(4, F)) :
    embSL4Mat σ (M * M') = embSL4Mat σ M * embSL4Mat σ M' := by
  rw [embSL4Mat, embSL4Mat, embSL4Mat, pairMat4_mul, lowBlk4_mul,
    Matrix.SpecialLinearGroup.coe_mul]

theorem embSL4Mat_one : embSL4Mat σ (1 : SL(4, F)) = 1 := by
  rw [embSL4Mat, lowBlk4_one, Matrix.SpecialLinearGroup.coe_one, pairMat4_one]

theorem embSL4Mat_isometry (hσ : ∀ c, σ (σ c) = c) (M : SL(4, F)) :
    conjTr σ (embSL4Mat σ M) * antidiag 8 * embSL4Mat σ M = antidiag 8 := by
  have hJ := antidiag_mul_self (F := F) 4
  have hJt := conjTr_antidiag (F := F) σ 4
  set J := (antidiag 4 : Matrix (Fin 4) (Fin 4) F)
  set Mi := ((M⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
  have hMi : Mi * (M : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have e1 : conjTr σ (M : Matrix (Fin 4) (Fin 4) F) * J * lowBlk4 σ M = J := by
    calc conjTr σ (M : Matrix (Fin 4) (Fin 4) F) * J * lowBlk4 σ M
        = conjTr σ (M : Matrix (Fin 4) (Fin 4) F) * (J * J) * conjTr σ Mi * J := by
          simp only [lowBlk4, Matrix.mul_assoc]; rfl
      _ = conjTr σ (Mi * (M : Matrix (Fin 4) (Fin 4) F)) * J := by
          rw [hJ, Matrix.mul_one, conjTr_mul]
      _ = J := by rw [hMi, conjTr_one, Matrix.one_mul]
  have e2 : conjTr σ (lowBlk4 σ M) * J * (M : Matrix (Fin 4) (Fin 4) F) = J := by
    have hc : conjTr σ (lowBlk4 σ M) = J * Mi * J := by
      simp only [lowBlk4, conjTr_mul, conjTr_conjTr_of_invol hσ]
      rw [hJt]
      simp only [Matrix.mul_assoc]
      rfl
    rw [hc]
    calc J * Mi * J * J * (M : Matrix (Fin 4) (Fin 4) F)
        = J * Mi * (J * J) * (M : Matrix (Fin 4) (Fin 4) F) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hJ, Matrix.mul_one, Matrix.mul_assoc, hMi, Matrix.mul_one]
  rw [embSL4Mat, conjTr_pairMat4, pairMat4_mul_antidiag_mul, e1, e2, antidiag_eight_eq]

@[expose] noncomputable def embSL4 (hσ : ∀ c, σ (σ c) = c) : SL(4, F) →* SU σ 8 where
  toFun M := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (embSL4Mat σ M)
      (by rw [det_embSL4Mat]; exact one_ne_zero), det_embSL4Mat σ M, embSL4Mat_isometry σ hσ M⟩
  map_one' := Subtype.ext (Units.ext (embSL4Mat_one σ))
  map_mul' M M' := Subtype.ext (Units.ext (embSL4Mat_mul σ M M'))

theorem coe_embSL4 (hσ : ∀ c, σ (σ c) = c) (M : SL(4, F)) :
    (((embSL4 σ hσ M : SU σ 8) : GL (Fin 8) F) : Matrix (Fin 8) (Fin 8) F) = embSL4Mat σ M :=
  rfl

theorem embSL4_injective (hσ : ∀ c, σ (σ c) = c) : Function.Injective (embSL4 σ hσ) := by
  intro M M' h
  have h' := congrArg (fun x : SU σ 8 => ((x : GL (Fin 8) F) : Matrix (Fin 8) (Fin 8) F)) h
  simp only [coe_embSL4] at h'
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  have := congrFun (congrFun h' ⟨i.val, by omega⟩) ⟨j.val, by omega⟩
  simpa [embSL4Mat, pairMat4_apply] using this

end CFSG.ClassicalInvolution.WeakCT.UnitaryEight

end
