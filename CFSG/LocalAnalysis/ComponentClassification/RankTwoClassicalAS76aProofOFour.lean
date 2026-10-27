module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCommute
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviSwap
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitExhaustion
public import CFSG.ClassicalGroups.Orthogonal.Matrix

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped MatrixGroups

section Shape

variable {K : Type} [Field K]

@[expose] def rhoOneShape (B : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (B 0 0 • 1) (B 0 1 • swapM) (B 1 0 • swapM) (B 1 1 • 1)

theorem rhoOneShape_smul (c : K) (B : Matrix (Fin 2) (Fin 2) K) :
    rhoOneShape (c • B) = c • rhoOneShape B := by
  simp only [rhoOneShape, Matrix.smul_apply, smul_eq_mul, fromBlocks_smul, smul_smul]

theorem rhoOneMat_eq_shape (B : SL(2, K)) :
    rhoOneMat B = rhoOneShape (B : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem eq_smul_swapM_of_commute {D : Matrix (Fin 2) (Fin 2) K}
    (h₁ : D * (1 + single 1 0 1) = (1 + single 0 1 1) * D)
    (h₂ : D * (1 + single 0 1 1) = (1 + single 1 0 1) * D) : D = D 0 1 • swapM := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h₁ h₂
  have e₁ := add_left_cancel h₁
  have e₂ := add_left_cancel h₂
  have a00 := congrFun (congrFun e₂ 0) 1
  have a10 := congrFun (congrFun e₁ 0) 0
  have a11 := congrFun (congrFun e₁ 1) 0
  simp [Matrix.mul_apply, single_apply] at a00 a10 a11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapM, a00, a11, ← a10]

theorem exists_rhoOneShape_of_commute {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h₁ : X * fromBlocks (1 + single 0 1 1) 0 0 (1 + single 1 0 1) =
      fromBlocks (1 + single 0 1 1) 0 0 (1 + single 1 0 1) * X)
    (h₂ : X * fromBlocks (1 + single 1 0 1) 0 0 (1 + single 0 1 1) =
      fromBlocks (1 + single 1 0 1) 0 0 (1 + single 0 1 1) * X) :
    ∃ B : Matrix (Fin 2) (Fin 2) K, X = rhoOneShape B := by
  rw [← fromBlocks_toBlocks X] at h₁ h₂ ⊢
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h₁ h₂
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h₁ h₂
  have hD₁ := eq_smul_one_of_commute_tr h₁.1 h₂.1
  have hD₄ := eq_smul_one_of_commute_tr h₂.2.2.2 h₁.2.2.2
  have hD₂ := eq_smul_swapM_of_commute h₁.2.1 h₂.2.1
  have hD₃ := eq_smul_swapM_of_commute h₂.2.2.1 h₁.2.2.1
  refine ⟨!![X.toBlocks₁₁ 0 0, X.toBlocks₁₂ 0 1; X.toBlocks₂₁ 0 1, X.toBlocks₂₂ 0 0], ?_⟩
  rw [rhoOneShape]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  rw [← hD₁, ← hD₂, ← hD₃, ← hD₄]

variable [CharP K 2]

theorem quadPlus_two_rhoOneShape (B : Matrix (Fin 2) (Fin 2) K) (u : Fin 2 ⊕ Fin 2 → K) :
    StatedQuadPlus 2 K (rhoOneShape B *ᵥ u) = B.det * StatedQuadPlus 2 K u := by
  rw [det_fin_two]
  simp only [StatedQuadPlus, Fin.sum_univ_two, rhoOneShape, mulVec, dotProduct,
    Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul, swapM, Matrix.add_apply,
    single_apply, Matrix.one_apply]
  simp
  linear_combination (B 0 0 * B 1 0 * u (.inl 0) * u (.inl 1) + B 0 1 * B 1 1 * u (.inr 0) *
    u (.inr 1) + B 0 1 * B 1 0 * (u (.inl 0) * u (.inr 0) + u (.inl 1) * u (.inr 1))) *
      CharTwo.two_eq_zero (R := K)

end Shape

section Coordinates

variable (K : Type) [Field K]

@[expose] def oMat : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun v := !![v (.inl 0), v (.inl 1); -v (.inr 1), v (.inr 0)]
  invFun X := Sum.elim ![X 0 0, X 0 1] ![X 1 1, -X 1 0]
  map_add' v w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  left_inv v := by
    funext s
    rcases s with i | i <;> fin_cases i <;> simp
  right_inv X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

variable {K}

theorem det_oMat (v : Fin 2 ⊕ Fin 2 → K) : (oMat K v).det = StatedQuadPlus 2 K v := by
  simp [oMat, Matrix.det_fin_two, StatedQuadPlus, Fin.sum_univ_two]

theorem oMat_apply (v : Fin 2 ⊕ Fin 2 → K) :
    oMat K v = !![v (.inl 0), v (.inl 1); -v (.inr 1), v (.inr 0)] := rfl

variable [CharP K 2]

theorem oMat_rhoOneShape (B : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 ⊕ Fin 2 → K) :
    oMat K (rhoOneShape B *ᵥ v) = B * oMat K v := by
  rw [oMat_apply, oMat_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rhoOneShape, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, swapM,
      single_apply, Matrix.mul_apply, CharTwo.neg_eq]

theorem oMat_rhoTwoMat (A : SL(2, K)) (v : Fin 2 ⊕ Fin 2 → K) :
    oMat K (rhoTwoMat A *ᵥ v) = oMat K v * (A : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  rw [oMat_apply, oMat_apply, rhoTwoMat_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, adjugate_fin_two,
      Matrix.mul_apply, CharTwo.neg_eq] <;> ring

omit [CharP K 2] in
theorem oMat_injective_mulVec {X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h : ∀ v, oMat K (X *ᵥ v) = oMat K (Y *ᵥ v)) : X = Y :=
  Matrix.ext_iff_mulVec.mpr fun v => (oMat K).injective (h v)

omit [CharP K 2] in
theorem exists_leftRight_of_isometry {X : GL (Fin 2 ⊕ Fin 2) K}
    (hX : ∀ v, StatedQuadPlus 2 K ((X : Matrix _ _ K) *ᵥ v) = StatedQuadPlus 2 K v) :
    ∃ A B : GL (Fin 2) K, (A : Matrix (Fin 2) (Fin 2) K).det = (B : Matrix (Fin 2) (Fin 2) K).det ∧
      ((∀ v, oMat K ((X : Matrix _ _ K) *ᵥ v) = (A : Matrix (Fin 2) (Fin 2) K) * oMat K v *
          ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) ∨
        ∀ v, oMat K ((X : Matrix _ _ K) *ᵥ v) = (A : Matrix (Fin 2) (Fin 2) K) * (oMat K v)ᵀ *
          ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
  set g : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K :=
    ((oMat K).symm.trans (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2) K X)).trans
      (oMat K)
  have hg : ∀ M, g M = oMat K ((X : Matrix _ _ K) *ᵥ (oMat K).symm M) := fun M => rfl
  have hgO : g ∈ DeterminantIsometries K := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
    fun M => by
      rw [determinantForm_apply, determinantForm_apply, hg, det_oMat, hX, ← det_oMat,
        LinearEquiv.apply_symm_apply]
  obtain ⟨z, hz | hz⟩ := determinant_isometry_exhaustion ⟨g, hgO⟩
  · refine ⟨z.val.1, z.val.2, (mem_equalDeterminants _ _).mp z.2, Or.inl fun v => ?_⟩
    have h := congrArg (fun φ : DeterminantIsometries K => φ.val (oMat K v)) hz
    simp only [hg, LinearEquiv.symm_apply_apply] at h
    rw [h, rho_apply]
  · refine ⟨z.val.1, z.val.2, (mem_equalDeterminants _ _).mp z.2, Or.inr fun v => ?_⟩
    have h := congrArg (fun φ : DeterminantIsometries K => φ.val (oMat K v)) hz
    simp only [hg, LinearEquiv.symm_apply_apply] at h
    rw [h, Subgroup.coe_mul, LinearEquiv.mul_apply, tau_apply, rho_apply]

theorem exists_leftRight_of_commute_five {ω : K} {X : GL (Fin 2 ⊕ Fin 2) K}
    (hX : ∀ v, StatedQuadPlus 2 K ((X : Matrix _ _ K) *ᵥ v) = StatedQuadPlus 2 K v)
    (hc : (X : Matrix _ _ K) * rhoOneShape (fiveM ω) = rhoOneShape (fiveM ω) * (X : Matrix _ _ K)) :
    ∃ A B : GL (Fin 2) K, (A : Matrix (Fin 2) (Fin 2) K).det = (B : Matrix (Fin 2) (Fin 2) K).det ∧
      (A : Matrix (Fin 2) (Fin 2) K) * fiveM ω = fiveM ω * A ∧
      ∀ v, oMat K ((X : Matrix _ _ K) *ᵥ v) = (A : Matrix (Fin 2) (Fin 2) K) * oMat K v *
        ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨A, B, hdet, h | h⟩ := exists_leftRight_of_isometry hX
  · refine ⟨A, B, hdet, ?_, h⟩
    have key := congrArg (oMat K) (congrFun (congrArg (· *ᵥ ·) hc) ((oMat K).symm B))
    simp only [← mulVec_mulVec, h, oMat_rhoOneShape, LinearEquiv.apply_symm_apply] at key
    have hBB : (B : Matrix (Fin 2) (Fin 2) K) * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (A : Matrix (Fin 2) (Fin 2) K) * fiveM ω =
        A * (fiveM ω * B) * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hBB, Matrix.mul_one]
      _ = fiveM ω * (A * B * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := key
      _ = fiveM ω * A := by
          rw [Matrix.mul_assoc (A : Matrix (Fin 2) (Fin 2) K), hBB, Matrix.mul_one]
  · exfalso
    have key : ∀ M : Matrix (Fin 2) (Fin 2) K,
        (A : Matrix (Fin 2) (Fin 2) K) * (fiveM ω * M)ᵀ = fiveM ω * (A * Mᵀ) := by
      intro M
      have k := congrArg (oMat K) (congrFun (congrArg (· *ᵥ ·) hc) ((oMat K).symm M))
      simp only [← mulVec_mulVec, h, oMat_rhoOneShape, LinearEquiv.apply_symm_apply] at k
      have k' := congrArg (· * (B : Matrix (Fin 2) (Fin 2) K)) k
      simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.mul_one] at k'
      exact k'
    have h1 := key 1
    rw [Matrix.mul_one, transpose_one, Matrix.mul_one] at h1
    have h2 := key (single 0 0 1)
    rw [transpose_mul, transpose_single, ← Matrix.mul_assoc, ← Matrix.mul_assoc (fiveM ω), ← h1,
      Matrix.mul_assoc, Matrix.mul_assoc] at h2
    have h3 := congrArg (((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ·) h2
    simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul] at h3
    have h4 := congrFun (congrFun h3 1) 0
    simp [fiveM, Matrix.mul_apply, single_apply] at h4

end Coordinates

end CFSG.ComponentClassification.RankTwoClassical
