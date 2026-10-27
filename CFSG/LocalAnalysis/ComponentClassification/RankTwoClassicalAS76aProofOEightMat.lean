module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOFour

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] [CharP K 2]

@[expose] def IsLeftRight (X : GL (Fin 2 ⊕ Fin 2) K) (A B : GL (Fin 2) K) : Prop :=
  ∀ v, oMat K ((X : Matrix _ _ K) *ᵥ v) = (A : Matrix (Fin 2) (Fin 2) K) * oMat K v *
    ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)

omit [CharP K 2] in
theorem gl_mul_inv_val (B : GL (Fin 2) K) :
    (B : Matrix (Fin 2) (Fin 2) K) * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

omit [CharP K 2] in
theorem gl_inv_mul_val (B : GL (Fin 2) K) :
    ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

namespace IsLeftRight

variable {X : GL (Fin 2 ⊕ Fin 2) K} {A B : GL (Fin 2) K}

omit [CharP K 2] in
theorem inv (h : IsLeftRight X A B) : IsLeftRight X⁻¹ A⁻¹ B⁻¹ := fun v => by
  have h1 := h (((X⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K) *ᵥ v)
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h1
  rw [inv_inv, h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, gl_inv_mul_val, Matrix.one_mul,
    Matrix.mul_assoc, gl_inv_mul_val, Matrix.mul_one]

theorem conj_rhoTwo (h : IsLeftRight X A B) (C : SL(2, K)) :
    ∃ C' : SL(2, K), (X : Matrix _ _ K) * rhoTwoMat C * ((X⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix _ _ K) = rhoTwoMat C' := by
  set b : Matrix (Fin 2) (Fin 2) K := (B : Matrix (Fin 2) (Fin 2) K)
  set b' : Matrix (Fin 2) (Fin 2) K := ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  have hbb : b * b' = 1 := gl_mul_inv_val B
  obtain ⟨C', hC'⟩ : ∃ C' : SL(2, K),
      (C' : Matrix (Fin 2) (Fin 2) K) = (b * (C : Matrix (Fin 2) (Fin 2) K)ᵀ * b')ᵀ :=
    ⟨⟨(b * (C : Matrix (Fin 2) (Fin 2) K)ᵀ * b')ᵀ, by
      rw [det_transpose, det_mul, det_mul, det_transpose, C.2, mul_one, ← det_mul, hbb,
        det_one]⟩, rfl⟩
  refine ⟨C', oMat_injective_mulVec fun v => ?_⟩
  rw [← mulVec_mulVec, ← mulVec_mulVec, h, oMat_rhoTwoMat, h.inv, oMat_rhoTwoMat C' v, hC',
    transpose_transpose]
  have hA : (A : Matrix (Fin 2) (Fin 2) K) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    1 := gl_mul_inv_val A
  simp only [inv_inv]
  calc (A : Matrix (Fin 2) (Fin 2) K) * (((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        oMat K v * b * (C : Matrix (Fin 2) (Fin 2) K)ᵀ) * b' =
      ((A : Matrix (Fin 2) (Fin 2) K) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
        oMat K v * (b * (C : Matrix (Fin 2) (Fin 2) K)ᵀ * b') := by
        simp only [Matrix.mul_assoc]
    _ = oMat K v * (b * (C : Matrix (Fin 2) (Fin 2) K)ᵀ * b') := by rw [hA, Matrix.one_mul]

theorem commutator (h : IsLeftRight X A B) {X' : GL (Fin 2 ⊕ Fin 2) K} {A' B' : GL (Fin 2) K}
    (h' : IsLeftRight X' A' B') (hAA : A * A' = A' * A) :
    ∃ C : SL(2, K), ((⁅X, X'⁆ : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K) = rhoTwoMat C := by
  set c : Matrix (Fin 2) (Fin 2) K := ((B' * B * B'⁻¹ * B⁻¹ : GL (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K)
  have hc : c.det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det (B' * B * B'⁻¹ * B⁻¹ : GL (Fin 2) K) = 1 := by
      rw [← commutatorElement_def, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact Commute.all _ _
    have h2 := congrArg Units.val h1
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h2
  obtain ⟨C', hC'⟩ : ∃ C' : SL(2, K), (C' : Matrix (Fin 2) (Fin 2) K) = cᵀ :=
    ⟨⟨cᵀ, by rw [det_transpose, hc]⟩, rfl⟩
  refine ⟨C', oMat_injective_mulVec fun v => ?_⟩
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec,
    ← mulVec_mulVec, ← mulVec_mulVec, h, h', h.inv, h'.inv, oMat_rhoTwoMat C' v, hC',
    transpose_transpose]
  simp only [inv_inv]
  have hA : ((A * A' * A⁻¹ * A'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [hAA, show A' * A * A⁻¹ * A'⁻¹ = 1 by group, Units.val_one]
  simp only [Units.val_mul] at hA
  have key : ∀ (a a' ai a'i b b' bi b'i M : Matrix (Fin 2) (Fin 2) K),
      a * (a' * (ai * (a'i * M * b') * b) * b'i) * bi =
        (a * a' * ai * a'i) * M * (b' * b * b'i * bi) := fun _ _ _ _ _ _ _ _ _ => by
    simp only [Matrix.mul_assoc]
  rw [key, hA, Matrix.one_mul]
  simp only [c, Units.val_mul]

end IsLeftRight

theorem isUnit_det_rhoOneShape_fiveM_sub_one {ω : K} (hω0 : ω ≠ 0) :
    IsUnit (rhoOneShape (fiveM ω) - 1).det := by
  have h : rhoOneShape (fiveM ω) - 1 = fromBlocks 1 swapM swapM ((ω + 1) • 1) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [rhoOneShape, fiveM, swapM, CharTwo.sub_eq_add]
  rw [h, det_fromBlocks_one₁₁, swapM_mul_swapM, add_smul, one_smul, add_sub_cancel_right,
    det_smul, Fintype.card_fin, det_one, mul_one]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hω0)

@[expose] def swapOneMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (single 0 0 1) (single 1 1 1) (single 1 1 1) (single 0 0 1)

omit [CharP K 2] in
theorem swapOneMat_mul_self : (swapOneMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
    swapOneMat = 1 := by
  rw [swapOneMat, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem oMat_swapOneMat (v : Fin 2 ⊕ Fin 2 → K) :
    oMat K (swapOneMat *ᵥ v) = (oMat K v)ᵀ := by
  rw [oMat_apply, oMat_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapOneMat, mulVec, dotProduct, Fintype.sum_sum_type, single_apply, CharTwo.neg_eq]

theorem quadPlus_two_swapOneMat (u : Fin 2 ⊕ Fin 2 → K) :
    StatedQuadPlus 2 K (swapOneMat *ᵥ u) = StatedQuadPlus 2 K u := by
  rw [← det_oMat, oMat_swapOneMat, det_transpose, det_oMat]

theorem swapOne_conj_rhoTwo (C : SL(2, K)) :
    swapOneMat * rhoTwoMat C * swapOneMat = rhoOneShape (C : Matrix (Fin 2) (Fin 2) K) := by
  refine oMat_injective_mulVec fun v => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, oMat_swapOneMat, oMat_rhoTwoMat, oMat_swapOneMat,
    oMat_rhoOneShape, transpose_mul, transpose_transpose, transpose_transpose]

theorem swapOne_conj_rhoOne (C : SL(2, K)) :
    swapOneMat * rhoOneShape (C : Matrix (Fin 2) (Fin 2) K) * swapOneMat = rhoTwoMat C := by
  refine oMat_injective_mulVec fun v => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, oMat_swapOneMat, oMat_rhoOneShape, oMat_swapOneMat,
    oMat_rhoTwoMat, transpose_mul, transpose_transpose]

end CFSG.ComponentClassification.RankTwoClassical
