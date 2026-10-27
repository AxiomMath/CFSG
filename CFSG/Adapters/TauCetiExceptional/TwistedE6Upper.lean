module

public import CFSG.Adapters.TauCetiExceptional.TwistedE6Block
import all TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.MinusculeWeight

public noncomputable section

namespace CFSG.TauCetiBridge.Twisted

open CFSG.Blueprint.Chevalley TauCeti TauCeti.DynkinType TauCeti.E6DoubledMinuscule
open scoped Matrix

variable {A : Type*} [CommRing A]

@[expose] def ulBlock (M : Matrix (Fin 54) (Fin 54) A) : Matrix (Fin 27) (Fin 27) A :=
  M.submatrix (fun a => matrixIndexEquiv (.inl a)) (fun a => matrixIndexEquiv (.inl a))

@[expose] def lrBlock (M : Matrix (Fin 54) (Fin 54) A) : Matrix (Fin 27) (Fin 27) A :=
  M.submatrix (fun a => matrixIndexEquiv (.inr a)) (fun a => matrixIndexEquiv (.inr a))

theorem e6Blk_inl (a : Fin 27) : e6Blk (matrixIndexEquiv (.inl a)) = 0 := by
  simp [e6Blk]

theorem e6Blk_inr (a : Fin 27) : e6Blk (matrixIndexEquiv (.inr a)) = 1 := by
  simp [e6Blk]

theorem ulBlock_mul {M N : Matrix (Fin 54) (Fin 54) A} (hM : IsBlockDiag e6Blk A M) :
    ulBlock (M * N) = ulBlock M * ulBlock N := by
  ext a b
  simp only [ulBlock, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← matrixIndexEquiv.sum_comp, Fintype.sum_sum_type]
  have h0 : ∀ y : Fin 27, M (matrixIndexEquiv (.inl a)) (matrixIndexEquiv (.inr y)) = 0 :=
    fun y => hM _ _ (by rw [e6Blk_inl, e6Blk_inr]; decide)
  simp only [h0, zero_mul, Finset.sum_const_zero, add_zero]

theorem lrBlock_mul {M N : Matrix (Fin 54) (Fin 54) A} (hM : IsBlockDiag e6Blk A M) :
    lrBlock (M * N) = lrBlock M * lrBlock N := by
  ext a b
  simp only [lrBlock, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← matrixIndexEquiv.sum_comp, Fintype.sum_sum_type]
  have h0 : ∀ y : Fin 27, M (matrixIndexEquiv (.inr a)) (matrixIndexEquiv (.inl y)) = 0 :=
    fun y => hM _ _ (by rw [e6Blk_inl, e6Blk_inr]; decide)
  simp only [h0, zero_mul, Finset.sum_const_zero, zero_add]

theorem ulBlock_one : ulBlock (1 : Matrix (Fin 54) (Fin 54) A) = 1 := by
  ext a b
  simp only [ulBlock, Matrix.submatrix_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq,
    Sum.inl.injEq]

theorem lrBlock_one : lrBlock (1 : Matrix (Fin 54) (Fin 54) A) = 1 := by
  ext a b
  simp only [lrBlock, Matrix.submatrix_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq,
    Sum.inr.injEq]

theorem ulBlock_add (M N : Matrix (Fin 54) (Fin 54) A) :
    ulBlock (M + N) = ulBlock M + ulBlock N := rfl

theorem lrBlock_add (M N : Matrix (Fin 54) (Fin 54) A) :
    lrBlock (M + N) = lrBlock M + lrBlock N := rfl

theorem ulBlock_smul (c : A) (M : Matrix (Fin 54) (Fin 54) A) :
    ulBlock (c • M) = c • ulBlock M := rfl

theorem lrBlock_smul (c : A) (M : Matrix (Fin 54) (Fin 54) A) :
    lrBlock (c • M) = c • lrBlock M := rfl

theorem ulBlock_rootIntMatrix_inl (i : Fin 6) :
    ulBlock (rootIntMatrix (.inl i)) = E6Minuscule.raisingMatrix i := by
  ext a b
  rw [ulBlock, Matrix.submatrix_apply, rootIntMatrix_inl_eq, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, raisingMatrix_apply,
    E6Minuscule.raisingMatrix_apply]
  simp

theorem lrBlock_rootIntMatrix_inl (i : Fin 6) :
    lrBlock (rootIntMatrix (.inl i)) = -E6Minuscule.loweringMatrix i := by
  ext a b
  rw [lrBlock, Matrix.submatrix_apply, rootIntMatrix_inl_eq, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, raisingMatrix_apply, Matrix.neg_apply,
    E6Minuscule.loweringMatrix_apply]
  simp only [e6DoubledMinusculeWeight_inr, Pi.neg_apply, reflection_inr, Sum.inr.injEq,
    neg_inj, summandSign_inr]
  by_cases h : e6MinusculeWeight b i = 1 ∧ a = e6MinusculeReflection i b <;> simp [h]

theorem ulBlock_rootIntMatrix_inr (i : Fin 6) :
    ulBlock (rootIntMatrix (.inr i)) = E6Minuscule.loweringMatrix i := by
  ext a b
  rw [ulBlock, Matrix.submatrix_apply, rootIntMatrix_inr_eq, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, loweringMatrix_apply,
    E6Minuscule.loweringMatrix_apply]
  simp

theorem lrBlock_rootIntMatrix_inr (i : Fin 6) :
    lrBlock (rootIntMatrix (.inr i)) = -E6Minuscule.raisingMatrix i := by
  ext a b
  rw [lrBlock, Matrix.submatrix_apply, rootIntMatrix_inr_eq, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, loweringMatrix_apply, Matrix.neg_apply,
    E6Minuscule.raisingMatrix_apply]
  simp only [e6DoubledMinusculeWeight_inr, Pi.neg_apply, reflection_inr, Sum.inr.injEq,
    summandSign_inr, neg_eq_iff_eq_neg]
  by_cases h : e6MinusculeWeight b i = -1 ∧ a = e6MinusculeReflection i b <;> simp [h]

theorem loweringMatrix_eq_transpose (i : Fin 6) :
    E6Minuscule.loweringMatrix i = (E6Minuscule.raisingMatrix i)ᵀ := by
  ext a b
  rw [Matrix.transpose_apply, E6Minuscule.loweringMatrix_apply, E6Minuscule.raisingMatrix_apply]
  revert i a b
  decide +kernel

variable (A) in
@[expose] def dualGL : Subgroup (Matrix.GeneralLinearGroup (Fin 54) A) where
  carrier := {g | g ∈ blockGL e6Blk A ∧
    (lrBlock (g : Matrix (Fin 54) (Fin 54) A))ᵀ * ulBlock (g : Matrix (Fin 54) (Fin 54) A) = 1}
  one_mem' := ⟨(blockGL e6Blk A).one_mem, by rw [Units.val_one, lrBlock_one, ulBlock_one,
    Matrix.transpose_one, Matrix.one_mul]⟩
  mul_mem' {g h} hg hh := ⟨(blockGL e6Blk A).mul_mem hg.1 hh.1, by
    rw [Units.val_mul, lrBlock_mul hg.1.1, ulBlock_mul hg.1.1, Matrix.transpose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc _ (ulBlock _), hg.2, Matrix.one_mul, hh.2]⟩
  inv_mem' {g} hg := ⟨(blockGL e6Blk A).inv_mem hg.1, by
    have hu : ulBlock (g : Matrix (Fin 54) (Fin 54) A) *
        ulBlock ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 54) A) :
          Matrix (Fin 54) (Fin 54) A) = 1 := by
      rw [← ulBlock_mul hg.1.1, ← Units.val_mul, mul_inv_cancel, Units.val_one, ulBlock_one]
    have hl : lrBlock ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A) *
        lrBlock (g : Matrix (Fin 54) (Fin 54) A) = 1 := by
      rw [← lrBlock_mul hg.1.2, ← Units.val_mul, inv_mul_cancel, Units.val_one, lrBlock_one]
    calc (lrBlock ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A))ᵀ *
          ulBlock ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A) =
        (lrBlock ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A))ᵀ *
          (((lrBlock (g : Matrix (Fin 54) (Fin 54) A))ᵀ *
            ulBlock (g : Matrix (Fin 54) (Fin 54) A)) *
          ulBlock ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 54) A) :
            Matrix (Fin 54) (Fin 54) A)) := by rw [hg.2, Matrix.one_mul]
      _ = (lrBlock (g : Matrix (Fin 54) (Fin 54) A) *
            lrBlock ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 54) A) :
              Matrix (Fin 54) (Fin 54) A))ᵀ *
          (ulBlock (g : Matrix (Fin 54) (Fin 54) A) *
            ulBlock ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 54) A) :
              Matrix (Fin 54) (Fin 54) A)) := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hu, Matrix.mul_one, mul_eq_one_comm.1 hl, Matrix.transpose_one]⟩

theorem ulBlock_map (M : Matrix (Fin 54) (Fin 54) ℤ) :
    ulBlock (M.map (Int.cast : ℤ → A)) = (ulBlock M).map (Int.cast : ℤ → A) := rfl

theorem lrBlock_map (M : Matrix (Fin 54) (Fin 54) ℤ) :
    lrBlock (M.map (Int.cast : ℤ → A)) = (lrBlock M).map (Int.cast : ℤ → A) := rfl

theorem transpose_mul_one_add_smul {X : Matrix (Fin 27) (Fin 27) ℤ} (hX : X ^ 2 = 0) (c : A) :
    (1 + c • (-Xᵀ).map (Int.cast : ℤ → A))ᵀ * (1 + c • X.map (Int.cast : ℤ → A)) = 1 := by
  have hX' : X.map (Int.cast : ℤ → A) * X.map (Int.cast : ℤ → A) = 0 := by
    have := congrArg (Int.castRingHom A).mapMatrix hX
    rw [map_pow, map_zero, pow_two] at this
    exact this
  have ht : ((-Xᵀ).map (Int.cast : ℤ → A))ᵀ = -X.map (Int.cast : ℤ → A) := by
    ext a b
    simp
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, ht, Matrix.add_mul,
    Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.neg_mul, smul_neg, smul_smul, hX', neg_zero, smul_zero, add_zero]
  abel

theorem rootSubgroupPoints_mem_dualGL (k : Fin 6 ⊕ Fin 6) (u : Multiplicative A) :
    (rootSubgroupPoints k A u : Matrix.GeneralLinearGroup (Fin 54) A) ∈ dualGL A := by
  have hbd : ∀ v : Multiplicative A, IsBlockDiag e6Blk A
      ((rootSubgroupPoints k A v : Matrix.GeneralLinearGroup (Fin 54) A) :
        Matrix (Fin 54) (Fin 54) A) := fun v => by
    rw [coe_rootSubgroupPoints_eq_one_add_smul]
    exact one_add_smul_isBlockDiag_e6 _ (rootIntMatrix_isBlockDiag k)
  refine ⟨mem_blockGL_of (hbd u) ?_, ?_⟩
  · rw [← Subgroup.coe_inv, ← map_inv]
    exact hbd _
  · rw [coe_rootSubgroupPoints_eq_one_add_smul, lrBlock_add, lrBlock_one, lrBlock_smul,
      lrBlock_map, ulBlock_add, ulBlock_one, ulBlock_smul, ulBlock_map]
    rcases k with i | i
    · rw [lrBlock_rootIntMatrix_inl, ulBlock_rootIntMatrix_inl, loweringMatrix_eq_transpose]
      exact transpose_mul_one_add_smul (E6Minuscule.raisingMatrix_pow_two i) _
    · rw [lrBlock_rootIntMatrix_inr, ulBlock_rootIntMatrix_inr, loweringMatrix_eq_transpose]
      have hX : (E6Minuscule.raisingMatrix i)ᵀ ^ 2 = 0 := by
        rw [← loweringMatrix_eq_transpose]
        exact E6Minuscule.loweringMatrix_pow_two i
      have h := transpose_mul_one_add_smul (A := A) hX (Multiplicative.toAdd u)
      rw [Matrix.transpose_transpose] at h
      exact h

@[expose] def dualPoly (a b : Fin 27) : MvPolynomial (Fin 54 × Fin 54) ℤ :=
  ∑ k : Fin 27, MvPolynomial.X (matrixIndexEquiv (.inr k), matrixIndexEquiv (.inr a)) *
      MvPolynomial.X (matrixIndexEquiv (.inl k), matrixIndexEquiv (.inl b)) -
    MvPolynomial.C (if a = b then 1 else 0)

theorem evalMat_dualPoly (M : Matrix (Fin 54) (Fin 54) A) (a b : Fin 27) :
    BigCell.evalMat M (dualPoly a b) = ((lrBlock M)ᵀ * ulBlock M - 1) a b := by
  simp only [dualPoly, map_sub, map_sum, map_mul, BigCell.evalMat_X, Matrix.sub_apply,
    Matrix.mul_apply, Matrix.transpose_apply, lrBlock, ulBlock, Matrix.submatrix_apply,
    Matrix.one_apply]
  congr 1
  rw [BigCell.evalMat, MvPolynomial.eval₂Hom_C]
  split_ifs <;> simp

theorem lrBlock_transpose_mul_ulBlock (g : Matrix.GeneralLinearGroup (Fin 54) A)
    (hg : g ∈ points A) :
    (lrBlock (g : Matrix (Fin 54) (Fin 54) A))ᵀ * ulBlock (g : Matrix (Fin 54) (Fin 54) A) = 1 := by
  have hle : elementarySubgroup ℚ ≤ (dualGL ℚ).comap (points ℚ).subtype := by
    rw [elementarySubgroup_le_iff]
    exact fun k u => rootSubgroupPoints_mem_dualGL k u
  rw [← sub_eq_zero]
  ext a b
  rw [Matrix.zero_apply, ← evalMat_dualPoly]
  refine e6d_evalMat_eq_zero _ (fun g' hg' => ?_) A g hg
  have h := (hle hg').2
  rw [evalMat_dualPoly]
  change ((lrBlock ((g' : Matrix.GeneralLinearGroup (Fin 54) ℚ) : Matrix (Fin 54) (Fin 54) ℚ))ᵀ *
    ulBlock ((g' : Matrix.GeneralLinearGroup (Fin 54) ℚ) : Matrix (Fin 54) (Fin 54) ℚ)) = 1 at h
  rw [h, sub_self, Matrix.zero_apply]

end CFSG.TauCetiBridge.Twisted
