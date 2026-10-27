module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOBlocks

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section Matrices

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}

theorem eq_oblk_of_commute {M : Matrix ι ι K} {H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hH : IsUnit (H - 1).det) (h : M * oblk oe 1 H = oblk oe 1 H * M) :
    ∃ (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K), M = oblk oe Y X := by
  obtain ⟨A, B, C, D, hM⟩ := eq_reindex_fromBlocks_oe (oe := oe) M
  rw [hM, oblk, ← map_mul, ← map_mul] at h
  have h' := (reindexAlgEquiv K K oe).injective h
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h'
  obtain ⟨-, hB, hC, -⟩ := h'
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Matrix.one_mul] at hB hC
  have hB0 : B = 0 := by
    have h0 : B * (H - 1) = 0 := by rw [Matrix.mul_sub, hB, Matrix.mul_one, sub_self]
    calc B = B * (H - 1) * (H - 1)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hH, Matrix.mul_one]
      _ = 0 := by rw [h0, Matrix.zero_mul]
  have hC0 : C = 0 := by
    have h0 : (H - 1) * C = 0 := by rw [Matrix.sub_mul, ← hC, Matrix.one_mul, sub_self]
    calc C = (H - 1)⁻¹ * ((H - 1) * C) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hH, Matrix.one_mul]
      _ = 0 := by rw [h0, Matrix.mul_zero]
  exact ⟨A, D, by rw [hM, hB0, hC0, oblk]⟩

end Matrices

section Four

variable {K : Type} [Field K]

theorem eq_smul_one_of_commute_tr {D : Matrix (Fin 2) (Fin 2) K}
    (h₁ : D * (1 + single 0 1 1) = (1 + single 0 1 1) * D)
    (h₂ : D * (1 + single 1 0 1) = (1 + single 1 0 1) * D) : D = D 0 0 • 1 := by
  have e₁ : single (0 : Fin 2) (1 : Fin 2) (1 : K) * D = D * single 0 1 1 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h₁
    exact (add_left_cancel h₁).symm
  have e₂ : single (1 : Fin 2) (0 : Fin 2) (1 : K) * D = D * single 1 0 1 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h₂
    exact (add_left_cancel h₂).symm
  obtain ⟨c, hc⟩ : D ∈ Set.range (scalar (Fin 2)) := by
    refine mem_range_scalar_of_commute_single fun i j hij => ?_
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact e₁
    · exact e₂
    · exact absurd rfl hij
  rw [← hc, scalar_apply, diagonal_apply_eq, smul_one_eq_diagonal]

theorem eq_smul_one_of_commute_rho {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h₁ : X * fromBlocks (1 + single 0 1 1) 0 0 (1 + single 1 0 1) =
      fromBlocks (1 + single 0 1 1) 0 0 (1 + single 1 0 1) * X)
    (h₂ : X * fromBlocks (1 + single 1 0 1) 0 0 (1 + single 0 1 1) =
      fromBlocks (1 + single 1 0 1) 0 0 (1 + single 0 1 1) * X)
    (h₃ : X * fromBlocks 1 swapM 0 1 = fromBlocks 1 swapM 0 1 * X)
    (h₄ : X * fromBlocks 1 0 swapM 1 = fromBlocks 1 0 swapM 1 * X) :
    X = X (.inl 0) (.inl 0) • 1 := by
  rw [← fromBlocks_toBlocks X] at h₁ h₂ h₃ h₄ ⊢
  set D₁ := X.toBlocks₁₁
  set D₂ := X.toBlocks₁₂
  set D₃ := X.toBlocks₂₁
  set D₄ := X.toBlocks₂₂
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h₁ h₂ h₃ h₄
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Matrix.one_mul] at h₁ h₂ h₃ h₄
  have hD₁ := eq_smul_one_of_commute_tr h₁.1 h₂.1
  have hD₄ := eq_smul_one_of_commute_tr h₂.2.2.2 h₁.2.2.2
  have hD₃ : D₃ = 0 := by
    have h0 : swapM * D₃ = 0 := by
      have := h₃.1
      rw [left_eq_add] at this
      exact this
    rw [← swapM_mul_swapM_mul D₃, h0, Matrix.mul_zero]
  have hD₂ : D₂ = 0 := by
    have h0 : D₂ * swapM = 0 := by
      have := h₄.1
      rw [add_eq_left] at this
      exact this
    rw [← mul_swapM_mul_swapM D₂, h0, Matrix.zero_mul]
  have hd : D₁ 0 0 = D₄ 0 0 := by
    have h5 := h₃.2.1
    rw [hD₁, hD₄] at h5
    have := congrFun (congrFun h5 0) 1
    simp [swapM] at this
    exact add_right_cancel (this.trans (add_comm _ _))
  rw [hD₂, hD₃, hD₁, hD₄, ← hd]
  simp only [fromBlocks_apply₁₁, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  rw [← fromBlocks_one, fromBlocks_smul, smul_zero]

theorem rhoTwoMat_tr_zero_one [CharP K 2] :
    rhoTwoMat (tr₂ (K := K) 0 1 (by decide)) =
      fromBlocks (1 + single 0 1 1) 0 0 (1 + single 1 0 1) := by
  rw [rhoTwoMat_apply]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tr₂, adjugate_fin_two, CharTwo.neg_eq]

theorem rhoTwoMat_tr_one_zero [CharP K 2] :
    rhoTwoMat (tr₂ (K := K) 1 0 (by decide)) =
      fromBlocks (1 + single 1 0 1) 0 0 (1 + single 0 1 1) := by
  rw [rhoTwoMat_apply]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tr₂, adjugate_fin_two, CharTwo.neg_eq]

theorem rhoOneMat_tr_zero_one :
    rhoOneMat (tr₂ (K := K) 0 1 (by decide)) = fromBlocks 1 swapM 0 1 := by
  rw [rhoOneMat_apply]
  simp [tr₂]

theorem rhoOneMat_tr_one_zero :
    rhoOneMat (tr₂ (K := K) 1 0 (by decide)) = fromBlocks 1 0 swapM 1 := by
  rw [rhoOneMat_apply]
  simp [tr₂]

end Four

section Centralizer

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : (ι → K) → K}
  {Q₂ : (ι₂ → K) → K}
  {hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b)))}
  {hSL : commutator SL(2, K) = ⊤}

@[expose] def oVec (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) (w : ι₂ → K) (u : Fin 2 ⊕ Fin 2 → K) :
    ι → K := fun i => Sum.elim w u (oe.symm i)

omit [Field K] [CharP K 2] [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem oVec_inl (w : ι₂ → K) (u : Fin 2 ⊕ Fin 2 → K) :
    (fun a => oVec oe w u (oe (.inl a))) = w := by
  funext a
  simp [oVec]

omit [Field K] [CharP K 2] [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem oVec_inr (w : ι₂ → K) (u : Fin 2 ⊕ Fin 2 → K) :
    (fun b => oVec oe w u (oe (.inr b))) = u := by
  funext b
  simp [oVec]

omit [CharP K 2] in
theorem exists_diag_sl2 {t : K} (ht0 : t ≠ 0) :
    ∃ A : SL(2, K), (A : Matrix (Fin 2) (Fin 2) K) = !![t, 0; 0, t⁻¹] :=
  ⟨⟨!![t, 0; 0, t⁻¹], by simp [det_fin_two, ht0]⟩, rfl⟩

theorem exists_oKappaGL_of_commute {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {g : StatedOmega Q}
    (h2 : ∀ A : SL(2, K), g * oRhoTwo oe hQ hSL A = oRhoTwo oe hQ hSL A * g)
    (h1 : ∀ B : SL(2, K), g * oRhoOne oe hQ hSL B = oRhoOne oe hQ hSL B * g) :
    ∃ Y : GL ι₂ K, (g : GL ι K) = oKappaGL oe Y ∧
      ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w := by
  have hm2 : ∀ A : SL(2, K), (g : GL ι K).val * oblk oe 1 (rhoTwoMat A) =
      oblk oe 1 (rhoTwoMat A) * (g : GL ι K).val := fun A => by
    have := congrArg (fun x : StatedOmega Q => ((x : GL ι K) : Matrix ι ι K)) (h2 A)
    simpa only [Subgroup.coe_mul, Units.val_mul, coe_oRhoTwo] using this
  have hm1 : ∀ B : SL(2, K), (g : GL ι K).val * oblk oe 1 (rhoOneMat B) =
      oblk oe 1 (rhoOneMat B) * (g : GL ι K).val := fun B => by
    have := congrArg (fun x : StatedOmega Q => ((x : GL ι K) : Matrix ι ι K)) (h1 B)
    simpa only [Subgroup.coe_mul, Units.val_mul, coe_oRhoOne] using this
  obtain ⟨A₀, hA₀⟩ := exists_diag_sl2 ht0
  have ht1' : t⁻¹ ≠ 1 := fun h => ht1 (by rw [← inv_inv t, h, inv_one])
  have hH : IsUnit (rhoTwoMat A₀ - 1).det := by
    have hdiag : rhoTwoMat A₀ - 1 =
        diagonal (Sum.elim ![t - 1, t⁻¹ - 1] ![t⁻¹ - 1, t - 1]) := by
      rw [rhoTwoMat_apply, hA₀, adjugate_fin_two]
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp
    rw [hdiag, det_diagonal]
    refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    rcases i with i | i <;> fin_cases i <;>
      simp [sub_ne_zero.mpr ht1, sub_ne_zero.mpr ht1']
  obtain ⟨Y, X, hYX⟩ := eq_oblk_of_commute hH (hm2 A₀)
  have hX : ∀ H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K,
      (g : GL ι K).val * oblk oe 1 H = oblk oe 1 H * (g : GL ι K).val → X * H = H * X := by
    intro H hgH
    rw [hYX, oblk_mul, oblk_mul, Matrix.mul_one, Matrix.one_mul] at hgH
    exact (oblk_injective hgH).2
  have hXc := eq_smul_one_of_commute_rho
    (hX _ (by rw [← rhoTwoMat_tr_zero_one]; exact hm2 _))
    (hX _ (by rw [← rhoTwoMat_tr_one_zero]; exact hm2 _))
    (hX _ (by rw [← rhoOneMat_tr_zero_one]; exact hm1 _))
    (hX _ (by rw [← rhoOneMat_tr_one_zero]; exact hm1 _))
  set c := X (.inl 0) (.inl 0)
  have hiso := quad_mulVec_of_mem_statedOmega g.2
  have hc : c = 1 := by
    set u₁ : Fin 2 ⊕ Fin 2 → K := Pi.single (.inl 0) 1 + Pi.single (.inr 0) 1
    have h3 := hiso (oVec oe 0 u₁)
    rw [hYX, quad_oblk_mulVec hQ, oVec_inl, oVec_inr, hQ, oVec_inl, oVec_inr, hXc,
      Matrix.mulVec_zero, smul_mulVec, Matrix.one_mulVec, add_right_inj] at h3
    have h4 : StatedQuadPlus 2 K (c • u₁) = c * c := by
      simp [StatedQuadPlus, Fin.sum_univ_two, u₁]
    have h5 : StatedQuadPlus 2 K u₁ = 1 := by
      simp [StatedQuadPlus, Fin.sum_univ_two, u₁]
    rw [h4, h5] at h3
    exact eq_of_mul_self_eq (h3.trans (mul_one 1).symm)
  rw [hc, one_smul] at hXc
  have hYiso : ∀ w, Q₂ (Y *ᵥ w) = Q₂ w := by
    intro w
    have h3 := hiso (oVec oe w 0)
    rw [hYX, quad_oblk_mulVec hQ, oVec_inl, oVec_inr, hQ, oVec_inl, oVec_inr, hXc,
      Matrix.mulVec_zero, add_left_inj] at h3
    exact h3
  have hYdet : Y.det ≠ 0 := by
    have h3 := ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (g : GL ι K))).ne_zero
    rw [hYX, det_oblk] at h3
    exact left_ne_zero_of_mul h3
  refine ⟨GeneralLinearGroup.mkOfDetNeZero Y hYdet, Units.ext ?_, hYiso⟩
  rw [coe_oKappaGL, hYX, hXc]
  rfl

end Centralizer

end CFSG.ComponentClassification.RankTwoClassical
