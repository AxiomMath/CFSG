module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviAut
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section TwoByTwo

variable {K : Type} [Field K]

@[expose] def twJ (ζ : K) : Matrix (Fin 2) (Fin 2) K := !![0, ζ⁻¹; ζ, 0]

theorem twJ_mul_twJ {ζ : K} (hζ0 : ζ ≠ 0) : twJ ζ * twJ ζ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twJ, Matrix.mul_apply, Fin.sum_univ_two, hζ0]

theorem transpose_swapM : (swapM : Matrix (Fin 2) (Fin 2) K)ᵀ = swapM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapM]

theorem transpose_twJ (ζ : K) : (twJ ζ)ᵀ = twJ ζ⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twJ]

theorem det_swapM_sub_twJ {ζ : K} (hζ1 : ζ ≠ 1) : (swapM - twJ ζ).det ≠ 0 := by
  have h : (swapM - twJ ζ).det = -((1 - ζ⁻¹) * (1 - ζ)) := by
    rw [det_fin_two]
    simp [swapM, twJ]
  rw [h, neg_ne_zero]
  refine mul_ne_zero (sub_ne_zero.mpr fun h1 => hζ1 ?_) (sub_ne_zero.mpr (Ne.symm hζ1))
  rw [← inv_inv ζ, ← h1, inv_one]

variable [CharP K 2]

theorem det_swapM : (swapM : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  rw [det_fin_two]
  simp [swapM, CharTwo.neg_eq]

theorem det_twJ {ζ : K} (hζ0 : ζ ≠ 0) : (twJ ζ).det = 1 := by
  rw [det_fin_two]
  simp [twJ, hζ0, CharTwo.neg_eq]

theorem eq_smul_one_of_commute_twJ {M : Matrix (Fin 2) (Fin 2) K} {ζ : K} (hζ0 : ζ ≠ 0)
    (hζ1 : ζ ≠ 1) (hJ : M * swapM = swapM * M) (hJ' : M * twJ ζ = twJ ζ * M) :
    M = M 0 0 • 1 := by
  have e1 := congrFun (congrFun hJ 0) 0
  have e2 := congrFun (congrFun hJ 0) 1
  have e3 := congrFun (congrFun hJ' 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, swapM, twJ, single_apply] at e1 e2 e3
  have hne : ζ - ζ⁻¹ ≠ 0 := by
    intro h0
    apply hζ1
    have h1 : ζ * ζ = 1 * 1 :=
      calc ζ * ζ = ζ⁻¹ * ζ := by rw [← sub_eq_zero.mp h0]
        _ = 1 * 1 := by rw [inv_mul_cancel₀ hζ0, mul_one]
    exact eq_of_mul_self_eq h1
  have hb : M 0 1 = 0 := by
    have h1 : M 0 1 * (ζ - ζ⁻¹) = 0 := by
      rw [mul_sub, e3, e1]
      ring
    exact (mul_eq_zero.mp h1).resolve_right hne
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp [hb]
  · simp [← e1, hb]
  · simp [e2]

end TwoByTwo

section Blocks

variable {K : Type} [Field K] {k : ℕ}

theorem eq_blk_of_mul_eq {M : Matrix (Fin (2 + k)) (Fin (2 + k)) K}
    {X₁ X₂ Y₁ Y₂ : Matrix (Fin 2) (Fin 2) K}
    (h₁ : M * blk Y₁ 1 = blk X₁ 1 * M) (h₂ : M * blk Y₂ 1 = blk X₂ 1 * M)
    (hX : (X₁ - X₂).det ≠ 0) (hY : (Y₁ - Y₂).det ≠ 0) :
    ∃ (M₁ : Matrix (Fin 2) (Fin 2) K) (D : Matrix (Fin k) (Fin k) K), M = blk M₁ D := by
  obtain ⟨A, B, C, D, hM⟩ := eq_reindex_fromBlocks M
  have key : ∀ {X Y : Matrix (Fin 2) (Fin 2) K}, M * blk Y 1 = blk X 1 * M →
      B = X * B ∧ C * Y = C := by
    intro X Y h
    rw [hM, blk, blk, ← map_mul, ← map_mul] at h
    have h' := (reindexAlgEquiv K K finSumFinEquiv).injective h
    rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h'
    obtain ⟨-, e2, e3, -⟩ := h'
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
      Matrix.one_mul] at e2 e3
    exact ⟨e2, e3⟩
  obtain ⟨hB₁, hC₁⟩ := key h₁
  obtain ⟨hB₂, hC₂⟩ := key h₂
  have hXu : IsUnit (X₁ - X₂) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hX)
  have hYu : IsUnit (Y₁ - Y₂) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hY)
  have hB : B = 0 := by
    have h0 : (X₁ - X₂) * B = 0 := by rw [Matrix.sub_mul, ← hB₁, ← hB₂, sub_self]
    calc B = (X₁ - X₂)⁻¹ * ((X₁ - X₂) * B) := by
          rw [← Matrix.mul_assoc,
            Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hXu), Matrix.one_mul]
      _ = 0 := by rw [h0, Matrix.mul_zero]
  have hC : C = 0 := by
    have h0 : C * (Y₁ - Y₂) = 0 := by rw [Matrix.mul_sub, hC₁, hC₂, sub_self]
    calc C = (C * (Y₁ - Y₂)) * (Y₁ - Y₂)⁻¹ := by
          rw [Matrix.mul_assoc,
            Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hYu), Matrix.mul_one]
      _ = 0 := by rw [h0, Matrix.zero_mul]
  exact ⟨A, D, by rw [hM, hB, hC, blk]⟩

theorem inv_val_of_blk {B : GL (Fin (2 + k)) K} {X : Matrix (Fin 2) (Fin 2) K}
    {D : Matrix (Fin k) (Fin k) K} (hB : B.val = blk X D) :
    (B⁻¹ : GL (Fin (2 + k)) K).val = blk X⁻¹ D⁻¹ ∧ X * X⁻¹ = 1 ∧ X⁻¹ * X = 1 ∧ D * D⁻¹ = 1 ∧
      D⁻¹ * D = 1 := by
  obtain ⟨hX, hD⟩ := det_ne_zero_of_blk hB
  have hXu : IsUnit X.det := isUnit_iff_ne_zero.mpr hX
  have hDu : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  refine ⟨?_, Matrix.mul_nonsing_inv _ hXu, Matrix.nonsing_inv_mul _ hXu,
    Matrix.mul_nonsing_inv _ hDu, Matrix.nonsing_inv_mul _ hDu⟩
  have h1 : B.val * blk X⁻¹ D⁻¹ = 1 := by
    rw [hB, blk_mul, Matrix.mul_nonsing_inv _ hXu, Matrix.mul_nonsing_inv _ hDu, blk_one]
  calc (B⁻¹ : GL (Fin (2 + k)) K).val = (B⁻¹ : GL (Fin (2 + k)) K).val * (B.val * blk X⁻¹ D⁻¹) :=
        by rw [h1, Matrix.mul_one]
    _ = blk X⁻¹ D⁻¹ := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

end Blocks

section Elements

variable {K : Type} [Field K] {f : ℕ}

theorem exists_statedSU_eq {n q : ℕ} {M : Matrix (Fin n) (Fin n) K} (hdet : M.det = 1)
    (hu : (M.map (· ^ q))ᵀ * M = 1) : ∃ g : StatedSU n q K, (g : GL (Fin n) K).val = M := by
  refine ⟨⟨GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero), ?_⟩, rfl⟩
  unfold StatedSU
  exact Subgroup.subset_closure ⟨hdet, hu⟩

variable [CharP K 2]

theorem exists_swapM_mem (f : ℕ) :
    ∃ g : StatedSU 2 (2 ^ f) K, (g : GL (Fin 2) K).val = swapM := by
  refine exists_statedSU_eq det_swapM ?_
  have hmap : (swapM : Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ f) = swapM := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swapM]
  rw [hmap, transpose_swapM, swapM_mul_swapM]

theorem exists_twJ_mem {ζ : K} (hζ : ζ ^ 2 ^ f * ζ = 1) :
    ∃ g : StatedSU 2 (2 ^ f) K, (g : GL (Fin 2) K).val = twJ ζ := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hζ
    exact zero_ne_one hζ
  have hq : ζ ^ 2 ^ f = ζ⁻¹ := eq_inv_of_mul_eq_one_left hζ
  refine exists_statedSU_eq (det_twJ hζ0) ?_
  have hmap : (twJ ζ).map (· ^ 2 ^ f) = twJ ζ⁻¹ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twJ, hq, inv_pow]
  rw [hmap, transpose_twJ, inv_inv, twJ_mul_twJ hζ0]

end Elements

section Diagonal

variable {K : Type} [Field K] {f k : ℕ}

theorem exists_diagonal_mem {d : Fin k → K} (hd : ∀ i, d i ^ 2 ^ f * d i = 1)
    (hdet : ∏ i, d i = 1) : ∃ g : StatedSU k (2 ^ f) K, (g : GL (Fin k) K).val = diagonal d := by
  refine exists_statedSU_eq (by rw [det_diagonal, hdet]) ?_
  rw [diagonal_map (by simp), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact hd i

theorem false_of_mul_diagonal {n : ℕ} {D : Matrix (Fin n) (Fin n) K} (hD : D.det ≠ 0)
    {s s' : Fin n → K} (h : D * diagonal s' = diagonal s * D) {j : Fin n}
    (hj : ∀ i, s i ≠ s' j) : False := by
  apply hD
  refine det_eq_zero_of_column_eq_zero j fun i => ?_
  have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j) h
  simp only [mul_diagonal, diagonal_mul] at h1
  have h2 : D i j * (s' j - s i) = 0 := by
    rw [mul_sub, h1]
    ring
  exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr (Ne.symm (hj i)))

variable [CharP K 2]

theorem exists_permMatrix_mem (π : Equiv.Perm (Fin k)) :
    ∃ g : StatedSU k (2 ^ f) K, (g : GL (Fin k) K).val = π.permMatrix K := by
  refine exists_statedSU_eq ?_ ?_
  · rw [det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h, CharTwo.neg_eq]
  · have hmap : (π.permMatrix K).map (· ^ 2 ^ f) = π.permMatrix K := by
      ext i j
      simp only [Equiv.Perm.permMatrix, Matrix.map_apply, PEquiv.toMatrix_apply]
      split_ifs <;> simp
    rw [hmap, Equiv.Perm.permMatrix, ← PEquiv.toMatrix_symm, ← PEquiv.toMatrix_trans,
      ← Equiv.toPEquiv_symm, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]

theorem sub_inv_ne_zero {ζ : K} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) : ζ - ζ⁻¹ ≠ 0 := by
  intro h0
  apply hζ1
  have h1 : ζ * ζ = 1 * 1 :=
    calc ζ * ζ = ζ⁻¹ * ζ := by rw [← sub_eq_zero.mp h0]
      _ = 1 * 1 := by rw [inv_mul_cancel₀ hζ0, mul_one]
  exact eq_of_mul_self_eq h1

theorem eq_smul_one_of_commute_statedSU (hk : 2 ≤ k) {ζ : K} (hζ : ζ ^ 2 ^ f * ζ = 1)
    (hζ1 : ζ ≠ 1) {D : Matrix (Fin k) (Fin k) K}
    (hD : ∀ g : StatedSU k (2 ^ f) K, D * (g : GL (Fin k) K).val = (g : GL (Fin k) K).val * D) :
    D = D ⟨0, by omega⟩ ⟨0, by omega⟩ • 1 := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hζ
    exact zero_ne_one hζ
  have hq : ζ ^ 2 ^ f = ζ⁻¹ := eq_inv_of_mul_eq_one_left hζ
  have hoff : ∀ r l : Fin k, r ≠ l → D r l = 0 := by
    intro r l hrl
    set d : Fin k → K := Function.update (Function.update 1 l ζ) r ζ⁻¹ with hd_def
    have hdr : d r = ζ⁻¹ := by simp [d]
    have hdl : d l = ζ := by simp [d, Ne.symm hrl]
    have hd : ∀ i, d i ^ 2 ^ f * d i = 1 := by
      intro i
      by_cases hi : i = r
      · rw [hi, hdr, inv_pow, hq, inv_inv, mul_inv_cancel₀ hζ0]
      · by_cases hil : i = l
        · rw [hil, hdl, hq, inv_mul_cancel₀ hζ0]
        · simp [d, hi, hil]
    have hdet : ∏ i, d i = 1 := by
      rw [hd_def, Finset.prod_update_of_mem (Finset.mem_univ r),
        Finset.prod_update_of_mem (by simp [Ne.symm hrl] : l ∈ Finset.univ \ {r})]
      simp [hζ0]
    obtain ⟨g, hg⟩ := exists_diagonal_mem hd hdet
    have h1 := congrArg (fun M : Matrix (Fin k) (Fin k) K => M r l) (hD g)
    simp only [hg, mul_diagonal, diagonal_mul, hdl, hdr] at h1
    have h2 : D r l * (ζ - ζ⁻¹) = 0 := by
      rw [mul_sub, h1]
      ring
    exact (mul_eq_zero.mp h2).resolve_right (sub_inv_ne_zero hζ0 hζ1)
  have hdiag : ∀ r l : Fin k, D r r = D l l := by
    intro r l
    by_cases hrl : r = l
    · rw [hrl]
    obtain ⟨g, hg⟩ := exists_permMatrix_mem (K := K) (f := f) (Equiv.swap r l)
    have h1 := congrArg (fun M : Matrix (Fin k) (Fin k) K => M r l) (hD g)
    simpa [hg, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv,
      PEquiv.toMatrix_toPEquiv_mul] using h1
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [hdiag i ⟨0, by omega⟩]
  · simp [hoff i j hij, hij]

end Diagonal

end CFSG.ComponentClassification.RankTwoClassical
