module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutPlane

public section

open CFSG CFSG.GH74 Subgroup Matrix
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

section Tvec

variable {F : Type} [Field F]

@[expose] def tvec (f ψ : Fin 4 → F) : Matrix (Fin 4) (Fin 4) F := 1 + Matrix.vecMulVec f ψ

theorem det_tvec (f ψ : Fin 4 → F) : (tvec f ψ).det = 1 + ψ ⬝ᵥ f := by
  rw [tvec, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]

@[expose] def tvecSL (f ψ : Fin 4 → F) (h : ψ ⬝ᵥ f = 0) : SL(4, F) :=
  ⟨tvec f ψ, by rw [det_tvec, h, add_zero]⟩

theorem coe_tvecSL (f ψ : Fin 4 → F) (h : ψ ⬝ᵥ f = 0) : (tvecSL f ψ h : Matrix (Fin 4) (Fin 4) F) = tvec f ψ := rfl

theorem tvec_mul_same (f ψ ψ' : Fin 4 → F) (h : ψ ⬝ᵥ f = 0) : tvec f ψ * tvec f ψ' = tvec f (ψ + ψ') := by
  simp only [tvec, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.vecMulVec_mul_vecMulVec, h, zero_smul,
    Matrix.vecMulVec_zero, add_zero, Matrix.vecMulVec_add, add_assoc]

theorem conj_tvec (M Mi : Matrix (Fin 4) (Fin 4) F) (hMi : M * Mi = 1) (f ψ : Fin 4 → F) :
    M * tvec f ψ * Mi = tvec (M *ᵥ f) (ψ ᵥ* Mi) := by
  simp only [tvec, mul_add, add_mul, Matrix.mul_one, hMi, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

theorem tvec_comm (f ψ g φ : Fin 4 → F) (hψf : ψ ⬝ᵥ f = 0) (hφg : φ ⬝ᵥ g = 0) (hψg : ψ ⬝ᵥ g = 0) :
    tvec f ψ * tvec g φ * tvec f (-ψ) * tvec g (-φ) = tvec g (-(φ ⬝ᵥ f) • ψ) := by
  have hPP : Matrix.vecMulVec f ψ * Matrix.vecMulVec f ψ = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hψf, zero_smul, Matrix.vecMulVec_zero]
  have hPQ : Matrix.vecMulVec f ψ * Matrix.vecMulVec g φ = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hψg, zero_smul, Matrix.vecMulVec_zero]
  have hQQ : Matrix.vecMulVec g φ * Matrix.vecMulVec g φ = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hφg, zero_smul, Matrix.vecMulVec_zero]
  have hQP : Matrix.vecMulVec g φ * Matrix.vecMulVec f ψ = (φ ⬝ᵥ f) • Matrix.vecMulVec g ψ := by
    rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
  have hRQ : Matrix.vecMulVec g ψ * Matrix.vecMulVec g φ = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hψg, zero_smul, Matrix.vecMulVec_zero]
  simp only [tvec, Matrix.vecMulVec_neg, Matrix.vecMulVec_smul, neg_smul, mul_add, add_mul, mul_neg, neg_mul,
    Matrix.one_mul, Matrix.mul_one, hPP, hPQ, hQQ, hQP, hRQ, add_zero, smul_zero, Matrix.smul_mul]
  abel

theorem tvec_dir_split (g1 g2 ψ : Fin 4 → F) (h2 : ψ ⬝ᵥ g2 = 0) : tvec g1 ψ * tvec g2 ψ = tvec (g1 + g2) ψ := by
  simp only [tvec, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.vecMulVec_mul_vecMulVec, h2, zero_smul,
    Matrix.vecMulVec_zero, add_zero, Matrix.add_vecMulVec, add_assoc]

theorem tvec_inv (f ψ : Fin 4 → F) (h : ψ ⬝ᵥ f = 0) : tvec f ψ * tvec f (-ψ) = 1 := by
  rw [tvec_mul_same f ψ (-ψ) h]
  simp [tvec]

theorem tvecSL_inv (f ψ : Fin 4 → F) (h : ψ ⬝ᵥ f = 0) :
    (tvecSL f ψ h)⁻¹ = tvecSL f (-ψ) (by rw [neg_dotProduct, h, neg_zero]) := by
  symm
  refine eq_inv_of_mul_eq_one_right ?_
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_tvecSL, coe_tvecSL, Matrix.SpecialLinearGroup.coe_one]
  exact tvec_inv f ψ h

theorem tvecSL_comm (f ψ g φ : Fin 4 → F) (hψf : ψ ⬝ᵥ f = 0) (hφg : φ ⬝ᵥ g = 0) (hψg : ψ ⬝ᵥ g = 0) :
    ⁅tvecSL f ψ hψf, tvecSL g φ hφg⁆ = tvecSL g (-(φ ⬝ᵥ f) • ψ)
      (by rw [smul_dotProduct, hψg, smul_zero]) := by
  rw [commutatorElement_def, tvecSL_inv, tvecSL_inv]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tvecSL]
  exact tvec_comm f ψ g φ hψf hφg hψg

theorem conj_tvecSL (x : SL(4, F)) (f ψ : Fin 4 → F) (h : ψ ⬝ᵥ f = 0) :
    x * tvecSL f ψ h * x⁻¹ = tvecSL ((x : Matrix (Fin 4) (Fin 4) F) *ᵥ f) (ψ ᵥ* ((x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F))
      (by
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one, h]) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tvecSL]
  exact conj_tvec _ _ (by rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]) f ψ

end Tvec

section RE

variable {F : Type} [Field F]

@[expose] def rE (α0 α1 β0 β1 γ0 γ1 δ0 δ1 : F) : Matrix (Fin 4) (Fin 4) F :=
  !![α0, -α1, β0, -β1; α1, α0, β1, β0; γ0, -γ1, δ0, -δ1; γ1, γ0, δ1, δ0]

@[expose] def rEinv (α0 α1 β0 β1 γ0 γ1 δ0 δ1 : F) : Matrix (Fin 4) (Fin 4) F :=
  !![δ0, -δ1, -β0, β1; δ1, δ0, -β1, -β0; -γ0, γ1, α0, -α1; -γ1, -γ0, α1, α0]

theorem rEinv_mul_rE (α0 α1 β0 β1 γ0 γ1 δ0 δ1 : F) (hu : α0 * δ0 - α1 * δ1 - β0 * γ0 + β1 * γ1 = 1)
    (hv : α0 * δ1 + α1 * δ0 - β0 * γ1 - β1 * γ0 = 0) :
    rEinv α0 α1 β0 β1 γ0 γ1 δ0 δ1 * rE α0 α1 β0 β1 γ0 γ1 δ0 δ1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rE, rEinv, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first | linear_combination hu | linear_combination hv | linear_combination (-1 : F) * hv | ring1

theorem det_rE (α0 α1 β0 β1 γ0 γ1 δ0 δ1 : F) :
    (rE α0 α1 β0 β1 γ0 γ1 δ0 δ1).det = (α0 * δ0 - α1 * δ1 - β0 * γ0 + β1 * γ1) ^ 2 +
      (α0 * δ1 + α1 * δ0 - β0 * γ1 - β1 * γ0) ^ 2 := by
  simp [rE, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

@[expose] def rEsl (α0 α1 β0 β1 γ0 γ1 δ0 δ1 : F) (hu : α0 * δ0 - α1 * δ1 - β0 * γ0 + β1 * γ1 = 1)
    (hv : α0 * δ1 + α1 * δ0 - β0 * γ1 - β1 * γ0 = 0) : SL(4, F) :=
  ⟨rE α0 α1 β0 β1 γ0 γ1 δ0 δ1, by rw [det_rE, hu, hv]; ring⟩

theorem coe_rEsl_inv (α0 α1 β0 β1 γ0 γ1 δ0 δ1 : F) (hu : α0 * δ0 - α1 * δ1 - β0 * γ0 + β1 * γ1 = 1)
    (hv : α0 * δ1 + α1 * δ0 - β0 * γ1 - β1 * γ0 = 0) :
    (((rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv)⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = rEinv α0 α1 β0 β1 γ0 γ1 δ0 δ1 := by
  have h1 : ((rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
      (((rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv)⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc (((rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv)⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
      = rEinv α0 α1 β0 β1 γ0 γ1 δ0 δ1 * (rE α0 α1 β0 β1 γ0 γ1 δ0 δ1 *
        (((rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv)⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)) := by
        rw [← Matrix.mul_assoc, rEinv_mul_rE α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv, Matrix.one_mul]
    _ = rEinv α0 α1 β0 β1 γ0 γ1 δ0 δ1 := by
        have : rE α0 α1 β0 β1 γ0 γ1 δ0 δ1 *
          (((rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv)⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = 1 := h1
        rw [this, Matrix.mul_one]

end RE

section PlanarMem

variable {F : Type} [Field F]

theorem trans01 (c : F) : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c = e12 c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e12, CFSG.LinearGroups.coe_transvection]

theorem trans10 (c : F) : Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c = e21 c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e21, CFSG.LinearGroups.coe_transvection]

theorem planar_mem_of_elem (Γ : Subgroup SL(4, F)) (h01 : ∀ a, tv 0 1 (by decide) a ∈ Γ)
    (h10 : ∀ a, tv 1 0 (by decide) a ∈ Γ) : ∀ g : SL(2, F), planar g ∈ Γ := by
  have : Γ.comap planarHom = ⊤ := by
    rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 2) (K := F)]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, j, hij, c, rfl⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · show planarHom _ ∈ Γ
      have h := h01 c
      rw [← planarHom_e12, ← trans01] at h
      exact h
    · show planarHom _ ∈ Γ
      have h := h10 c
      rw [← planarHom_e21, ← trans10] at h
      exact h
    · exact absurd rfl hij
  intro g
  have := (eq_top_iff.1 this) (Subgroup.mem_top g)
  exact this

theorem tvecSL_L_mem (Γ : Subgroup SL(4, F)) (hG : ∀ g : SL(2, F), planar g ∈ Γ) (f ψ : Fin 4 → F)
    (hf2 : f 2 = 0) (hf3 : f 3 = 0) (hψ2 : ψ 2 = 0) (hψ3 : ψ 3 = 0) (h : ψ ⬝ᵥ f = 0) : tvecSL f ψ h ∈ Γ := by
  have h' : f 0 * ψ 0 + f 1 * ψ 1 = 0 := by
    simp only [dotProduct, Fin.sum_univ_four, hf2, hf3, hψ2, hψ3, mul_zero, add_zero] at h
    linear_combination h
  let g : SL(2, F) := ⟨!![1 + f 0 * ψ 0, f 0 * ψ 1; f 1 * ψ 0, 1 + f 1 * ψ 1], by
    rw [Matrix.det_fin_two_of]; linear_combination h'⟩
  have : tvecSL f ψ h = planar g := by
    apply Subtype.ext
    rw [coe_tvecSL, coe_planar]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tvec, Matrix.vecMulVec_apply, hf2, hf3, hψ2, hψ3, g]
  rw [this]
  exact hG g

end PlanarMem

section Opt

variable {F : Type} [Field F]

theorem opt1 (Γ : Subgroup SL(4, F)) (hG : ∀ g : SL(2, F), planar g ∈ Γ) (r : SL(4, F)) (hr : r ∈ Γ)
    (f ψ fy ψy : Fin 4 → F) (hf2 : f 2 = 0) (hf3 : f 3 = 0) (hψ2 : ψ 2 = 0) (hψ3 : ψ 3 = 0)
    (hfy2 : fy 2 = 0) (hfy3 : fy 3 = 0) (hψy2 : ψy 2 = 0) (hψy3 : ψy 3 = 0)
    (hψf : ψ ⬝ᵥ f = 0) (hψyfy : ψy ⬝ᵥ fy = 0) (hcross : ψ ⬝ᵥ ((r : Matrix (Fin 4) (Fin 4) F) *ᵥ fy) = 0)
    (g' ψ' : Fin 4 → F) (hg' : g' = (r : Matrix (Fin 4) (Fin 4) F) *ᵥ fy)
    (hψ' : ψ' = (-((ψy ᵥ* ((r⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)) ⬝ᵥ f)) • ψ) (h' : ψ' ⬝ᵥ g' = 0) :
    tvecSL g' ψ' h' ∈ Γ := by
  have hx : tvecSL f ψ hψf ∈ Γ := tvecSL_L_mem Γ hG f ψ hf2 hf3 hψ2 hψ3 hψf
  have hy : tvecSL fy ψy hψyfy ∈ Γ := tvecSL_L_mem Γ hG fy ψy hfy2 hfy3 hψy2 hψy3 hψyfy
  have hc : ⁅tvecSL f ψ hψf, r * tvecSL fy ψy hψyfy * r⁻¹⁆ ∈ Γ := by
    rw [commutatorElement_def]
    exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hx (Γ.mul_mem (Γ.mul_mem hr hy) (Γ.inv_mem hr))) (Γ.inv_mem hx))
      (Γ.inv_mem (Γ.mul_mem (Γ.mul_mem hr hy) (Γ.inv_mem hr)))
  rw [conj_tvecSL] at hc
  have hψg : ψ ⬝ᵥ ((r : Matrix (Fin 4) (Fin 4) F) *ᵥ fy) = 0 := hcross
  rw [tvecSL_comm f ψ _ _ hψf _ hψg] at hc
  subst hg' hψ'
  exact hc

theorem opt2 (Γ : Subgroup SL(4, F)) (hG : ∀ g : SL(2, F), planar g ∈ Γ) (r : SL(4, F)) (hr : r ∈ Γ)
    (g φ fy ψy : Fin 4 → F) (hg2 : g 2 = 0) (hg3 : g 3 = 0) (hφ2 : φ 2 = 0) (hφ3 : φ 3 = 0)
    (hfy2 : fy 2 = 0) (hfy3 : fy 3 = 0) (hψy2 : ψy 2 = 0) (hψy3 : ψy 3 = 0)
    (hφg : φ ⬝ᵥ g = 0) (hψyfy : ψy ⬝ᵥ fy = 0)
    (hcross : (ψy ᵥ* ((r⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)) ⬝ᵥ g = 0)
    (ψ' : Fin 4 → F)
    (hψ' : ψ' = (-(φ ⬝ᵥ ((r : Matrix (Fin 4) (Fin 4) F) *ᵥ fy))) • (ψy ᵥ* ((r⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)))
    (h' : ψ' ⬝ᵥ g = 0) : tvecSL g ψ' h' ∈ Γ := by
  have hx : tvecSL g φ hφg ∈ Γ := tvecSL_L_mem Γ hG g φ hg2 hg3 hφ2 hφ3 hφg
  have hy : tvecSL fy ψy hψyfy ∈ Γ := tvecSL_L_mem Γ hG fy ψy hfy2 hfy3 hψy2 hψy3 hψyfy
  have hc : ⁅r * tvecSL fy ψy hψyfy * r⁻¹, tvecSL g φ hφg⁆ ∈ Γ := by
    rw [commutatorElement_def]
    exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hr hy) (Γ.inv_mem hr)) hx)
      (Γ.inv_mem (Γ.mul_mem (Γ.mul_mem hr hy) (Γ.inv_mem hr)))) (Γ.inv_mem hx)
  rw [conj_tvecSL] at hc
  rw [tvecSL_comm _ _ g φ _ hφg hcross] at hc
  subst hψ'
  exact hc

theorem peelA (Γ : Subgroup SL(4, F)) (hG : ∀ g : SL(2, F), planar g ∈ Γ) (g1 g2 ψ : Fin 4 → F)
    (hg12 : g1 2 = 0) (hg13 : g1 3 = 0) (hψ2 : ψ 2 = 0) (hψ3 : ψ 3 = 0) (hψg1 : ψ ⬝ᵥ g1 = 0) (hψg2 : ψ ⬝ᵥ g2 = 0)
    (h : ψ ⬝ᵥ (g1 + g2) = 0) (hmem : tvecSL (g1 + g2) ψ h ∈ Γ) : tvecSL g2 ψ hψg2 ∈ Γ := by
  have h1 : tvecSL g1 ψ hψg1 ∈ Γ := tvecSL_L_mem Γ hG g1 ψ hg12 hg13 hψ2 hψ3 hψg1
  have e : tvecSL (g1 + g2) ψ h = tvecSL g1 ψ hψg1 * tvecSL g2 ψ hψg2 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tvecSL]
    exact (tvec_dir_split g1 g2 ψ hψg2).symm
  have : tvecSL g2 ψ hψg2 = (tvecSL g1 ψ hψg1)⁻¹ * tvecSL (g1 + g2) ψ h := by
    rw [e]; group
  rw [this]
  exact Γ.mul_mem (Γ.inv_mem h1) hmem

theorem peelB (Γ : Subgroup SL(4, F)) (hG : ∀ g : SL(2, F), planar g ∈ Γ) (g ψ1 ψ2 : Fin 4 → F)
    (hg2 : g 2 = 0) (hg3 : g 3 = 0) (hψ12 : ψ1 2 = 0) (hψ13 : ψ1 3 = 0) (hψ1g : ψ1 ⬝ᵥ g = 0) (hψ2g : ψ2 ⬝ᵥ g = 0)
    (h : (ψ1 + ψ2) ⬝ᵥ g = 0) (hmem : tvecSL g (ψ1 + ψ2) h ∈ Γ) : tvecSL g ψ2 hψ2g ∈ Γ := by
  have h1 : tvecSL g ψ1 hψ1g ∈ Γ := tvecSL_L_mem Γ hG g ψ1 hg2 hg3 hψ12 hψ13 hψ1g
  have e : tvecSL g (ψ1 + ψ2) h = tvecSL g ψ1 hψ1g * tvecSL g ψ2 hψ2g := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tvecSL]
    exact (tvec_mul_same g ψ1 ψ2 hψ1g).symm
  have : tvecSL g ψ2 hψ2g = (tvecSL g ψ1 hψ1g)⁻¹ * tvecSL g (ψ1 + ψ2) h := by
    rw [e]; group
  rw [this]
  exact Γ.mul_mem (Γ.inv_mem h1) hmem

theorem coe_rEsl (α0 α1 β0 β1 γ0 γ1 δ0 δ1 : F) (hu : α0 * δ0 - α1 * δ1 - β0 * γ0 + β1 * γ1 = 1)
    (hv : α0 * δ1 + α1 * δ0 - β0 * γ1 - β1 * γ0 = 0) :
    ((rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = rE α0 α1 β0 β1 γ0 γ1 δ0 δ1 := rfl

theorem comp1 (Γ : Subgroup SL(4, F)) (hG : ∀ g : SL(2, F), planar g ∈ Γ) (α0 α1 β0 β1 γ0 γ1 δ0 δ1 : F)
    (hu : α0 * δ0 - α1 * δ1 - β0 * γ0 + β1 * γ1 = 1) (hv : α0 * δ1 + α1 * δ0 - β0 * γ1 - β1 * γ0 = 0)
    (hr : rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv ∈ Γ) (hm : α0 * δ1 + α1 * δ0 ≠ 0) (t : F)
    (h : (![0, t, 0, 0] : Fin 4 → F) ⬝ᵥ ![0, 0, γ0 * α0 + γ1 * α1, γ1 * α0 - γ0 * α1] = 0) :
    tvecSL ![0, 0, γ0 * α0 + γ1 * α1, γ1 * α0 - γ0 * α1] ![0, t, 0, 0] h ∈ Γ := by
  have hcoe := coe_rEsl_inv α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv
  have key := opt1 Γ hG (rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv) hr ![-t / (α0 * δ1 + α1 * δ0), 0, 0, 0] ![0, 1, 0, 0]
    ![α0, -α1, 0, 0] ![α1, α0, 0, 0] (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp [dotProduct, Fin.sum_univ_four]) (by simp [dotProduct, Fin.sum_univ_four]; ring)
    (by simp [coe_rEsl, rE, Matrix.mulVec, dotProduct, Fin.sum_univ_four]; ring)
    (![α0 * α0 + α1 * α1, 0, 0, 0] + ![0, 0, γ0 * α0 + γ1 * α1, γ1 * α0 - γ0 * α1]) ![0, t, 0, 0]
    (by
      ext i; fin_cases i <;> simp [coe_rEsl, rE, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      all_goals ring)
    (by
      rw [hcoe]
      ext i; fin_cases i <;> simp [rEinv, Matrix.vecMul, dotProduct, Fin.sum_univ_four]
      all_goals (try field_simp)
      all_goals (try ring))
    (by simp [dotProduct, Fin.sum_univ_four])
  exact peelA Γ hG ![α0 * α0 + α1 * α1, 0, 0, 0] ![0, 0, γ0 * α0 + γ1 * α1, γ1 * α0 - γ0 * α1] ![0, t, 0, 0]
    (by simp) (by simp) (by simp) (by simp) (by simp [dotProduct, Fin.sum_univ_four]) h
    (by simp [dotProduct, Fin.sum_univ_four]) key

theorem comp2 (Γ : Subgroup SL(4, F)) (hG : ∀ g : SL(2, F), planar g ∈ Γ) (α0 α1 β0 β1 γ0 γ1 δ0 δ1 : F)
    (hu : α0 * δ0 - α1 * δ1 - β0 * γ0 + β1 * γ1 = 1) (hv : α0 * δ1 + α1 * δ0 - β0 * γ1 - β1 * γ0 = 0)
    (hr : rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv ∈ Γ) (hm : α0 * δ1 + α1 * δ0 ≠ 0) (t : F)
    (h : (![t, 0, 0, 0] : Fin 4 → F) ⬝ᵥ ![0, 0, -(γ1 * α0 - γ0 * α1), γ0 * α0 + γ1 * α1] = 0) :
    tvecSL ![0, 0, -(γ1 * α0 - γ0 * α1), γ0 * α0 + γ1 * α1] ![t, 0, 0, 0] h ∈ Γ := by
  have hcoe := coe_rEsl_inv α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv
  have key := opt1 Γ hG (rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv) hr ![0, -t / (α0 * δ1 + α1 * δ0), 0, 0] ![1, 0, 0, 0]
    ![α1, α0, 0, 0] ![-α0, α1, 0, 0] (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp [dotProduct, Fin.sum_univ_four]) (by simp [dotProduct, Fin.sum_univ_four]; ring)
    (by simp [coe_rEsl, rE, Matrix.mulVec, dotProduct, Fin.sum_univ_four]; ring)
    (![0, α0 * α0 + α1 * α1, 0, 0] + ![0, 0, -(γ1 * α0 - γ0 * α1), γ0 * α0 + γ1 * α1]) ![t, 0, 0, 0]
    (by
      ext i; fin_cases i <;> simp [coe_rEsl, rE, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      all_goals ring)
    (by
      rw [hcoe]
      ext i; fin_cases i <;> simp [rEinv, Matrix.vecMul, dotProduct, Fin.sum_univ_four]
      all_goals (try field_simp))
    (by simp [dotProduct, Fin.sum_univ_four])
  exact peelA Γ hG ![0, α0 * α0 + α1 * α1, 0, 0] ![0, 0, -(γ1 * α0 - γ0 * α1), γ0 * α0 + γ1 * α1] ![t, 0, 0, 0]
    (by simp) (by simp) (by simp) (by simp) (by simp [dotProduct, Fin.sum_univ_four]) h
    (by simp [dotProduct, Fin.sum_univ_four]) key

theorem comp3 (Γ : Subgroup SL(4, F)) (hG : ∀ g : SL(2, F), planar g ∈ Γ) (α0 α1 β0 β1 γ0 γ1 δ0 δ1 : F)
    (hu : α0 * δ0 - α1 * δ1 - β0 * γ0 + β1 * γ1 = 1) (hv : α0 * δ1 + α1 * δ0 - β0 * γ1 - β1 * γ0 = 0)
    (hr : rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv ∈ Γ) (σ : F)
    (h : (![0, 0, (α0 * δ1 + α1 * δ0) * (δ0 * β1 - δ1 * β0), (α0 * δ1 + α1 * δ0) * (δ0 * β0 + δ1 * β1)] : Fin 4 → F) ⬝ᵥ
      ![σ, 0, 0, 0] = 0) :
    tvecSL ![σ, 0, 0, 0] ![0, 0, (α0 * δ1 + α1 * δ0) * (δ0 * β1 - δ1 * β0), (α0 * δ1 + α1 * δ0) * (δ0 * β0 + δ1 * β1)] h ∈ Γ := by
  have hcoe := coe_rEsl_inv α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv
  have key := opt2 Γ hG (rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv) hr ![σ, 0, 0, 0] ![0, 1, 0, 0]
    ![δ0, δ1, 0, 0] ![-δ1, δ0, 0, 0] (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp [dotProduct, Fin.sum_univ_four]) (by simp [dotProduct, Fin.sum_univ_four]; ring)
    (by
      rw [hcoe]
      simp [rEinv, Matrix.vecMul, dotProduct, Fin.sum_univ_four, -mul_eq_zero]; ring)
    (![0, -((α0 * δ1 + α1 * δ0) * (δ0 * δ0 + δ1 * δ1)), 0, 0] +
      ![0, 0, (α0 * δ1 + α1 * δ0) * (δ0 * β1 - δ1 * β0), (α0 * δ1 + α1 * δ0) * (δ0 * β0 + δ1 * β1)])
    (by
      rw [hcoe]
      ext i; fin_cases i <;> simp [coe_rEsl, rE, rEinv, Matrix.mulVec, dotProduct, Fin.sum_univ_four, -mul_eq_zero, -zero_eq_mul, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      all_goals ring)
    (by simp [dotProduct, Fin.sum_univ_four])
  exact peelB Γ hG ![σ, 0, 0, 0] ![0, -((α0 * δ1 + α1 * δ0) * (δ0 * δ0 + δ1 * δ1)), 0, 0]
    ![0, 0, (α0 * δ1 + α1 * δ0) * (δ0 * β1 - δ1 * β0), (α0 * δ1 + α1 * δ0) * (δ0 * β0 + δ1 * β1)]
    (by simp) (by simp) (by simp) (by simp) (by simp [dotProduct, Fin.sum_univ_four]) h
    (by simp [dotProduct, Fin.sum_univ_four]) key

theorem comp4 (Γ : Subgroup SL(4, F)) (hG : ∀ g : SL(2, F), planar g ∈ Γ) (α0 α1 β0 β1 γ0 γ1 δ0 δ1 : F)
    (hu : α0 * δ0 - α1 * δ1 - β0 * γ0 + β1 * γ1 = 1) (hv : α0 * δ1 + α1 * δ0 - β0 * γ1 - β1 * γ0 = 0)
    (hr : rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv ∈ Γ) (σ : F)
    (h : (![0, 0, (α0 * δ1 + α1 * δ0) * (δ0 * β0 + δ1 * β1), -((α0 * δ1 + α1 * δ0) * (δ0 * β1 - δ1 * β0))] : Fin 4 → F) ⬝ᵥ
      ![0, σ, 0, 0] = 0) :
    tvecSL ![0, σ, 0, 0] ![0, 0, (α0 * δ1 + α1 * δ0) * (δ0 * β0 + δ1 * β1),
      -((α0 * δ1 + α1 * δ0) * (δ0 * β1 - δ1 * β0))] h ∈ Γ := by
  have hcoe := coe_rEsl_inv α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv
  have key := opt2 Γ hG (rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv) hr ![0, σ, 0, 0] ![1, 0, 0, 0]
    ![-δ1, δ0, 0, 0] ![-δ0, -δ1, 0, 0] (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp [dotProduct, Fin.sum_univ_four]) (by simp [dotProduct, Fin.sum_univ_four]; ring)
    (by
      rw [hcoe]
      simp [rEinv, Matrix.vecMul, dotProduct, Fin.sum_univ_four, -mul_eq_zero]; ring)
    (![-((α0 * δ1 + α1 * δ0) * (δ0 * δ0 + δ1 * δ1)), 0, 0, 0] +
      ![0, 0, (α0 * δ1 + α1 * δ0) * (δ0 * β0 + δ1 * β1), -((α0 * δ1 + α1 * δ0) * (δ0 * β1 - δ1 * β0))])
    (by
      rw [hcoe]
      ext i; fin_cases i <;> simp [coe_rEsl, rE, rEinv, Matrix.mulVec, dotProduct, Fin.sum_univ_four, -mul_eq_zero, -zero_eq_mul, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      all_goals ring)
    (by simp [dotProduct, Fin.sum_univ_four])
  exact peelB Γ hG ![0, σ, 0, 0] ![-((α0 * δ1 + α1 * δ0) * (δ0 * δ0 + δ1 * δ1)), 0, 0, 0]
    ![0, 0, (α0 * δ1 + α1 * δ0) * (δ0 * β0 + δ1 * β1), -((α0 * δ1 + α1 * δ0) * (δ0 * β1 - δ1 * β0))]
    (by simp) (by simp) (by simp) (by simp) (by simp [dotProduct, Fin.sum_univ_four]) h
    (by simp [dotProduct, Fin.sum_univ_four]) key

end Opt

section WeylSpan

variable {F : Type} [Field F]

@[expose] def WHi : Matrix (Fin 4) (Fin 4) F := !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem coe_wH_inv : (((wH : SL(4, F))⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = WHi := by
  have h1 : ((wH : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * ((((wH : SL(4, F))⁻¹ : SL(4, F))) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h2 : (WHi : Matrix (Fin 4) (Fin 4) F) * ((wH : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [coe_wH]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [WHi, Matrix.mul_apply, Fin.sum_univ_four]
  calc ((((wH : SL(4, F))⁻¹ : SL(4, F))) : Matrix (Fin 4) (Fin 4) F)
      = WHi * (((wH : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * ((((wH : SL(4, F))⁻¹ : SL(4, F))) : Matrix (Fin 4) (Fin 4) F)) := by
        rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
    _ = WHi := by rw [h1, Matrix.mul_one]

theorem weyl_mem (Γ : Subgroup SL(4, F)) (hw : (wH : SL(4, F)) ∈ Γ) (f ψ : Fin 4 → F) (h : ψ ⬝ᵥ f = 0)
    (hmem : tvecSL f ψ h ∈ Γ) (f' ψ' : Fin 4 → F) (hf' : f' = ((wH : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *ᵥ f)
    (hψ' : ψ' = ψ ᵥ* (WHi : Matrix (Fin 4) (Fin 4) F)) (h' : ψ' ⬝ᵥ f' = 0) : tvecSL f' ψ' h' ∈ Γ := by
  have h1 : wH * tvecSL f ψ h * wH⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem hw hmem) (Γ.inv_mem hw)
  have hMi : ((wH : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * WHi = 1 := by
    rw [← coe_wH_inv, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have e : wH * tvecSL f ψ h * wH⁻¹ = tvecSL f' ψ' h' := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tvecSL]
    rw [coe_wH_inv, conj_tvec _ _ hMi f ψ, hf', hψ']
  rw [← e]
  exact h1

theorem tvecSL_scal (a b : F) (f ψ : Fin 4 → F) (h1 : ψ ⬝ᵥ ((a * b) • f) = 0) (h2 : (b • ψ) ⬝ᵥ (a • f) = 0) :
    tvecSL ((a * b) • f) ψ h1 = tvecSL (a • f) (b • ψ) h2 := by
  apply Subtype.ext
  rw [coe_tvecSL, coe_tvecSL]
  simp only [tvec, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, mul_comm]

theorem cramer2 (p q r s u v : F) (hΔ : p * s - q * r ≠ 0) :
    ∃ x y : F, x * p + y * r = u ∧ x * q + y * s = v := by
  have hΔ' : s * p - r * q ≠ 0 := fun h => hΔ (by linear_combination h)
  refine ⟨(u * s - v * r) / (p * s - q * r), (p * v - q * u) / (p * s - q * r), ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring

theorem spanA (Γ : Subgroup SL(4, F)) (ψ D1 D2 : Fin 4 → F) (hψ2 : ψ 2 = 0) (hψ3 : ψ 3 = 0)
    (hD10 : D1 0 = 0) (hD11 : D1 1 = 0) (hD20 : D2 0 = 0) (hD21 : D2 1 = 0)
    (hdet : D1 2 * D2 3 - D1 3 * D2 2 ≠ 0)
    (H1 : ∀ (σ : F) (h : ψ ⬝ᵥ (σ • D1) = 0), tvecSL (σ • D1) ψ h ∈ Γ)
    (H2 : ∀ (σ : F) (h : ψ ⬝ᵥ (σ • D2) = 0), tvecSL (σ • D2) ψ h ∈ Γ) :
    ∀ (D : Fin 4 → F), D 0 = 0 → D 1 = 0 → ∀ (a : F) (h : ψ ⬝ᵥ (a • D) = 0), tvecSL (a • D) ψ h ∈ Γ := by
  intro D hD0 hD1 a h
  obtain ⟨μ1, μ2, e2, e3⟩ := cramer2 (D1 2) (D1 3) (D2 2) (D2 3) (D 2) (D 3) hdet
  have hdec : a • D = (a * μ1) • D1 + (a * μ2) • D2 := by
    ext i
    fin_cases i
    · simp [hD0, hD10, hD20]
    · simp [hD1, hD11, hD21]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk]
      linear_combination a * (-e2)
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk]
      linear_combination a * (-e3)
  have hp1 : ψ ⬝ᵥ ((a * μ1) • D1) = 0 := by
    simp only [dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul, hψ2, hψ3, hD10, hD11]
    ring
  have hp2 : ψ ⬝ᵥ ((a * μ2) • D2) = 0 := by
    simp only [dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul, hψ2, hψ3, hD20, hD21]
    ring
  have e : tvecSL (a • D) ψ h = tvecSL ((a * μ1) • D1) ψ hp1 * tvecSL ((a * μ2) • D2) ψ hp2 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tvecSL]
    rw [tvec_dir_split _ _ _ hp2, ← hdec]
  rw [e]
  exact Γ.mul_mem (H1 _ hp1) (H2 _ hp2)

theorem spanQ (Γ : Subgroup SL(4, F)) (g K1 K2 : Fin 4 → F) (hg2 : g 2 = 0) (hg3 : g 3 = 0)
    (hK10 : K1 0 = 0) (hK11 : K1 1 = 0) (hK20 : K2 0 = 0) (hK21 : K2 1 = 0)
    (hdet : K1 2 * K2 3 - K1 3 * K2 2 ≠ 0)
    (H1 : ∀ (σ : F) (h : K1 ⬝ᵥ (σ • g) = 0), tvecSL (σ • g) K1 h ∈ Γ)
    (H2 : ∀ (σ : F) (h : K2 ⬝ᵥ (σ • g) = 0), tvecSL (σ • g) K2 h ∈ Γ) :
    ∀ (K : Fin 4 → F), K 0 = 0 → K 1 = 0 → ∀ (a : F) (h : K ⬝ᵥ (a • g) = 0), tvecSL (a • g) K h ∈ Γ := by
  intro K hK0 hK1 a h
  obtain ⟨l1, l2, e2, e3⟩ := cramer2 (K1 2) (K1 3) (K2 2) (K2 3) (K 2) (K 3) hdet
  have hdec : K = l1 • K1 + l2 • K2 := by
    ext i
    fin_cases i
    · simp [hK0, hK10, hK20]
    · simp [hK1, hK11, hK21]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk]
      linear_combination -e2
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk]
      linear_combination -e3
  have hp1 : (l1 • K1) ⬝ᵥ (a • g) = 0 := by
    simp only [dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul, hg2, hg3, hK10, hK11]
    ring
  have hp2 : (l2 • K2) ⬝ᵥ (a • g) = 0 := by
    simp only [dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul, hg2, hg3, hK20, hK21]
    ring
  have e : tvecSL (a • g) K h = tvecSL (a • g) (l1 • K1) hp1 * tvecSL (a • g) (l2 • K2) hp2 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tvecSL]
    rw [tvec_mul_same _ _ _ hp1, ← hdec]
  have hm1 : tvecSL (a • g) (l1 • K1) hp1 ∈ Γ := by
    have := H1 (a * l1) (by
      simp only [dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul, hg2, hg3, hK10, hK11]; ring)
    have e' : tvecSL ((a * l1) • g) K1 (by
        simp only [dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul, hg2, hg3, hK10, hK11]; ring) =
        tvecSL (a • g) (l1 • K1) hp1 := by
      exact tvecSL_scal a l1 g K1 _ hp1
    rw [← e']
    exact this
  have hm2 : tvecSL (a • g) (l2 • K2) hp2 ∈ Γ := by
    have := H2 (a * l2) (by
      simp only [dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul, hg2, hg3, hK20, hK21]; ring)
    have e' : tvecSL ((a * l2) • g) K2 (by
        simp only [dotProduct, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul, hg2, hg3, hK20, hK21]; ring) =
        tvecSL (a • g) (l2 • K2) hp2 := by
      exact tvecSL_scal a l2 g K2 _ hp2
    rw [← e']
    exact this
  rw [e]
  exact Γ.mul_mem hm1 hm2

theorem tv_eq_tvecSL (i j : Fin 4) (hij : i ≠ j) (a : F) :
    tv i j hij a = tvecSL (a • (Pi.single i (1 : F))) (Pi.single j (1 : F))
      (by simp [dotProduct, Pi.single_apply, hij]) := by
  apply Subtype.ext
  rw [coe_tv, coe_tvecSL]
  ext k l
  simp [tvec, Matrix.vecMulVec_apply, Matrix.single_apply, Pi.single_apply, Matrix.one_apply]
  by_cases hk : k = i
  · subst hk
    by_cases hl : l = j
    · subst hl; simp
    · simp [hl, Ne.symm hl]
  · by_cases hl : l = j
    · subst hl; simp [hk, Ne.symm hk]
    · simp [hl, Ne.symm hk, Ne.symm hl]

theorem tvecSL_eq_of (f ψ f' ψ' : Fin 4 → F) (h : ψ ⬝ᵥ f = 0) (h' : ψ' ⬝ᵥ f' = 0) (he : tvec f ψ = tvec f' ψ') :
    tvecSL f ψ h = tvecSL f' ψ' h' := Subtype.ext he

theorem tv_mem_of (Γ : Subgroup SL(4, F)) (i j : Fin 4) (hij : i ≠ j) (a : F) (D ψ : Fin 4 → F)
    (hD : D = Pi.single i 1) (hψ : ψ = Pi.single j 1) (h : ψ ⬝ᵥ (a • D) = 0) (hmem : tvecSL (a • D) ψ h ∈ Γ) :
    tv i j hij a ∈ Γ := by
  subst hD hψ
  rw [tv_eq_tvecSL]
  exact hmem

theorem Qminus_roots (Γ : Subgroup SL(4, F)) (hG : ∀ g : SL(2, F), planar g ∈ Γ) (hw : (wH : SL(4, F)) ∈ Γ)
    (α0 α1 β0 β1 γ0 γ1 δ0 δ1 : F) (hu : α0 * δ0 - α1 * δ1 - β0 * γ0 + β1 * γ1 = 1)
    (hv : α0 * δ1 + α1 * δ0 - β0 * γ1 - β1 * γ0 = 0) (hr : rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv ∈ Γ)
    (hm : α0 * δ1 + α1 * δ0 ≠ 0)
    (hN : (γ0 * α0 + γ1 * α1) * (γ0 * α0 + γ1 * α1) + (γ1 * α0 - γ0 * α1) * (γ1 * α0 - γ0 * α1) ≠ 0) :
    ∀ a : F, tv 2 0 (by decide) a ∈ Γ ∧ tv 3 0 (by decide) a ∈ Γ ∧ tv 2 1 (by decide) a ∈ Γ ∧
      tv 3 1 (by decide) a ∈ Γ := by
  have C1 : ∀ t h, tvecSL ![0, 0, γ0 * α0 + γ1 * α1, γ1 * α0 - γ0 * α1] ![0, t, 0, 0] h ∈ Γ :=
    fun t h => comp1 Γ hG α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv hr hm t h
  have C2 : ∀ t h, tvecSL ![0, 0, -(γ1 * α0 - γ0 * α1), γ0 * α0 + γ1 * α1] ![t, 0, 0, 0] h ∈ Γ :=
    fun t h => comp2 Γ hG α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv hr hm t h
  have C1w : ∀ t h, tvecSL ![0, 0, γ0 * α0 + γ1 * α1, γ1 * α0 - γ0 * α1] ![t, 0, 0, 0] h ∈ Γ := fun t h =>
    weyl_mem Γ hw _ _ (by simp [dotProduct, Fin.sum_univ_four]) (C1 (-t) (by simp [dotProduct, Fin.sum_univ_four]))
      _ _ (by
        ext i; fin_cases i <;> simp [coe_wH, Matrix.mulVec, dotProduct, Fin.sum_univ_four]) (by
        ext i; fin_cases i <;> simp [WHi, Matrix.vecMul, dotProduct, Fin.sum_univ_four]) h
  have C2w : ∀ t h, tvecSL ![0, 0, -(γ1 * α0 - γ0 * α1), γ0 * α0 + γ1 * α1] ![0, t, 0, 0] h ∈ Γ := fun t h =>
    weyl_mem Γ hw _ _ (by simp [dotProduct, Fin.sum_univ_four]) (C2 t (by simp [dotProduct, Fin.sum_univ_four]))
      _ _ (by
        ext i; fin_cases i <;> simp [coe_wH, Matrix.mulVec, dotProduct, Fin.sum_univ_four]) (by
        ext i; fin_cases i <;> simp [WHi, Matrix.vecMul, dotProduct, Fin.sum_univ_four]) h
  set g2 := γ0 * α0 + γ1 * α1 with hg2
  set g3 := γ1 * α0 - γ0 * α1 with hg3
  have S0 := spanA Γ ![1, 0, 0, 0] ![0, 0, -g3, g2] ![0, 0, g2, g3] (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp; intro h; apply hN; linear_combination -h)
    (fun σ h => by
      rw [tvecSL_eq_of (σ • ![0, 0, -g3, g2]) ![1, 0, 0, 0] ![0, 0, -g3, g2] ![σ, 0, 0, 0] h
        (by simp [dotProduct, Fin.sum_univ_four]) (by
          ext i j; fin_cases i <;> fin_cases j <;> simp [tvec] <;> ring)]
      exact C2 σ _)
    (fun σ h => by
      rw [tvecSL_eq_of (σ • ![0, 0, g2, g3]) ![1, 0, 0, 0] ![0, 0, g2, g3] ![σ, 0, 0, 0] h
        (by simp [dotProduct, Fin.sum_univ_four]) (by
          ext i j; fin_cases i <;> fin_cases j <;> simp [tvec] <;> ring)]
      exact C1w σ _)
  have S1 := spanA Γ ![0, 1, 0, 0] ![0, 0, g2, g3] ![0, 0, -g3, g2] (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp; intro h; apply hN; linear_combination h)
    (fun σ h => by
      rw [tvecSL_eq_of (σ • ![0, 0, g2, g3]) ![0, 1, 0, 0] ![0, 0, g2, g3] ![0, σ, 0, 0] h
        (by simp [dotProduct, Fin.sum_univ_four]) (by
          ext i j; fin_cases i <;> fin_cases j <;> simp [tvec] <;> ring)]
      exact C1 σ _)
    (fun σ h => by
      rw [tvecSL_eq_of (σ • ![0, 0, -g3, g2]) ![0, 1, 0, 0] ![0, 0, -g3, g2] ![0, σ, 0, 0] h
        (by simp [dotProduct, Fin.sum_univ_four]) (by
          ext i j; fin_cases i <;> fin_cases j <;> simp [tvec] <;> ring)]
      exact C2w σ _)
  intro a
  refine ⟨tv_mem_of Γ 2 0 (by decide) a ![0, 0, 1, 0] ![1, 0, 0, 0] (by ext i; fin_cases i <;> simp)
      (by ext i; fin_cases i <;> simp) (by simp [dotProduct, Fin.sum_univ_four]) (S0 ![0, 0, 1, 0] (by simp) (by simp) a _),
    tv_mem_of Γ 3 0 (by decide) a ![0, 0, 0, 1] ![1, 0, 0, 0] (by ext i; fin_cases i <;> simp)
      (by ext i; fin_cases i <;> simp) (by simp [dotProduct, Fin.sum_univ_four]) (S0 ![0, 0, 0, 1] (by simp) (by simp) a _),
    tv_mem_of Γ 2 1 (by decide) a ![0, 0, 1, 0] ![0, 1, 0, 0] (by ext i; fin_cases i <;> simp)
      (by ext i; fin_cases i <;> simp) (by simp [dotProduct, Fin.sum_univ_four]) (S1 ![0, 0, 1, 0] (by simp) (by simp) a _),
    tv_mem_of Γ 3 1 (by decide) a ![0, 0, 0, 1] ![0, 1, 0, 0] (by ext i; fin_cases i <;> simp)
      (by ext i; fin_cases i <;> simp) (by simp [dotProduct, Fin.sum_univ_four]) (S1 ![0, 0, 0, 1] (by simp) (by simp) a _)⟩

theorem Q_roots (Γ : Subgroup SL(4, F)) (hG : ∀ g : SL(2, F), planar g ∈ Γ) (hw : (wH : SL(4, F)) ∈ Γ)
    (α0 α1 β0 β1 γ0 γ1 δ0 δ1 : F) (hu : α0 * δ0 - α1 * δ1 - β0 * γ0 + β1 * γ1 = 1)
    (hv : α0 * δ1 + α1 * δ0 - β0 * γ1 - β1 * γ0 = 0) (hr : rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv ∈ Γ)
    (hm : α0 * δ1 + α1 * δ0 ≠ 0)
    (hN : (δ0 * β1 - δ1 * β0) * (δ0 * β1 - δ1 * β0) + (δ0 * β0 + δ1 * β1) * (δ0 * β0 + δ1 * β1) ≠ 0) :
    ∀ a : F, tv 0 2 (by decide) a ∈ Γ ∧ tv 0 3 (by decide) a ∈ Γ ∧ tv 1 2 (by decide) a ∈ Γ ∧
      tv 1 3 (by decide) a ∈ Γ := by
  have Q3 : ∀ σ h, tvecSL ![σ, 0, 0, 0] ![0, 0, (α0 * δ1 + α1 * δ0) * (δ0 * β1 - δ1 * β0),
      (α0 * δ1 + α1 * δ0) * (δ0 * β0 + δ1 * β1)] h ∈ Γ :=
    fun σ h => comp3 Γ hG α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv hr σ h
  have Q4 : ∀ σ h, tvecSL ![0, σ, 0, 0] ![0, 0, (α0 * δ1 + α1 * δ0) * (δ0 * β0 + δ1 * β1),
      -((α0 * δ1 + α1 * δ0) * (δ0 * β1 - δ1 * β0))] h ∈ Γ :=
    fun σ h => comp4 Γ hG α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv hr σ h
  have Q3w : ∀ σ h, tvecSL ![0, σ, 0, 0] ![0, 0, (α0 * δ1 + α1 * δ0) * (δ0 * β1 - δ1 * β0),
      (α0 * δ1 + α1 * δ0) * (δ0 * β0 + δ1 * β1)] h ∈ Γ := fun σ h =>
    weyl_mem Γ hw _ _ (by simp [dotProduct, Fin.sum_univ_four]) (Q3 σ (by simp [dotProduct, Fin.sum_univ_four]))
      _ _ (by
        ext i; fin_cases i <;> simp [coe_wH, Matrix.mulVec, dotProduct, Fin.sum_univ_four]) (by
        ext i; fin_cases i <;> simp [WHi, Matrix.vecMul, dotProduct, Fin.sum_univ_four]) h
  have Q4w : ∀ σ h, tvecSL ![σ, 0, 0, 0] ![0, 0, (α0 * δ1 + α1 * δ0) * (δ0 * β0 + δ1 * β1),
      -((α0 * δ1 + α1 * δ0) * (δ0 * β1 - δ1 * β0))] h ∈ Γ := fun σ h =>
    weyl_mem Γ hw _ _ (by simp [dotProduct, Fin.sum_univ_four]) (Q4 (-σ) (by simp [dotProduct, Fin.sum_univ_four]))
      _ _ (by
        ext i; fin_cases i <;> simp [coe_wH, Matrix.mulVec, dotProduct, Fin.sum_univ_four]) (by
        ext i; fin_cases i <;> simp [WHi, Matrix.vecMul, dotProduct, Fin.sum_univ_four]) h
  set m := α0 * δ1 + α1 * δ0 with hmdef
  set k2 := δ0 * β1 - δ1 * β0 with hk2
  set k3 := δ0 * β0 + δ1 * β1 with hk3
  have hdet : m * k2 * -(m * k2) - m * k3 * (m * k3) ≠ 0 := by
    intro h
    apply mul_ne_zero (mul_ne_zero hm hm) hN
    linear_combination -h
  have hdet' : m * k3 * (m * k3) - -(m * k2) * (m * k2) ≠ 0 := by
    intro h
    apply mul_ne_zero (mul_ne_zero hm hm) hN
    linear_combination h
  have S0 := spanQ Γ ![1, 0, 0, 0] ![0, 0, m * k2, m * k3] ![0, 0, m * k3, -(m * k2)] (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simpa using hdet)
    (fun σ h => by
      rw [tvecSL_eq_of (σ • ![1, 0, 0, 0]) ![0, 0, m * k2, m * k3] ![σ, 0, 0, 0] ![0, 0, m * k2, m * k3] h
        (by simp [dotProduct, Fin.sum_univ_four]) (by
          ext i j; fin_cases i <;> fin_cases j <;> simp [tvec])]
      exact Q3 σ _)
    (fun σ h => by
      rw [tvecSL_eq_of (σ • ![1, 0, 0, 0]) ![0, 0, m * k3, -(m * k2)] ![σ, 0, 0, 0] ![0, 0, m * k3, -(m * k2)] h
        (by simp [dotProduct, Fin.sum_univ_four]) (by
          ext i j; fin_cases i <;> fin_cases j <;> simp [tvec])]
      exact Q4w σ _)
  have S1 := spanQ Γ ![0, 1, 0, 0] ![0, 0, m * k2, m * k3] ![0, 0, m * k3, -(m * k2)] (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simpa using hdet)
    (fun σ h => by
      rw [tvecSL_eq_of (σ • ![0, 1, 0, 0]) ![0, 0, m * k2, m * k3] ![0, σ, 0, 0] ![0, 0, m * k2, m * k3] h
        (by simp [dotProduct, Fin.sum_univ_four]) (by
          ext i j; fin_cases i <;> fin_cases j <;> simp [tvec])]
      exact Q3w σ _)
    (fun σ h => by
      rw [tvecSL_eq_of (σ • ![0, 1, 0, 0]) ![0, 0, m * k3, -(m * k2)] ![0, σ, 0, 0] ![0, 0, m * k3, -(m * k2)] h
        (by simp [dotProduct, Fin.sum_univ_four]) (by
          ext i j; fin_cases i <;> fin_cases j <;> simp [tvec])]
      exact Q4 σ _)
  intro a
  refine ⟨tv_mem_of Γ 0 2 (by decide) a ![1, 0, 0, 0] ![0, 0, 1, 0] (by ext i; fin_cases i <;> simp)
      (by ext i; fin_cases i <;> simp) (by simp [dotProduct, Fin.sum_univ_four]) (S0 ![0, 0, 1, 0] (by simp) (by simp) a _),
    tv_mem_of Γ 0 3 (by decide) a ![1, 0, 0, 0] ![0, 0, 0, 1] (by ext i; fin_cases i <;> simp)
      (by ext i; fin_cases i <;> simp) (by simp [dotProduct, Fin.sum_univ_four]) (S0 ![0, 0, 0, 1] (by simp) (by simp) a _),
    tv_mem_of Γ 1 2 (by decide) a ![0, 1, 0, 0] ![0, 0, 1, 0] (by ext i; fin_cases i <;> simp)
      (by ext i; fin_cases i <;> simp) (by simp [dotProduct, Fin.sum_univ_four]) (S1 ![0, 0, 1, 0] (by simp) (by simp) a _),
    tv_mem_of Γ 1 3 (by decide) a ![0, 1, 0, 0] ![0, 0, 0, 1] (by ext i; fin_cases i <;> simp)
      (by ext i; fin_cases i <;> simp) (by simp [dotProduct, Fin.sum_univ_four]) (S1 ![0, 0, 0, 1] (by simp) (by simp) a _)⟩

theorem top_of_roots (Γ : Subgroup SL(4, F)) (h01 : ∀ a, tv 0 1 (by decide) a ∈ Γ) (h10 : ∀ a, tv 1 0 (by decide) a ∈ Γ)
    (t20 : ∀ a, tv 2 0 (by decide) a ∈ Γ) (t30 : ∀ a, tv 3 0 (by decide) a ∈ Γ) (t21 : ∀ a, tv 2 1 (by decide) a ∈ Γ)
    (t31 : ∀ a, tv 3 1 (by decide) a ∈ Γ) (t02 : ∀ a, tv 0 2 (by decide) a ∈ Γ) (t03 : ∀ a, tv 0 3 (by decide) a ∈ Γ)
    (t12 : ∀ a, tv 1 2 (by decide) a ∈ Γ) (t13 : ∀ a, tv 1 3 (by decide) a ∈ Γ) : Γ = ⊤ := by
  have t23 : ∀ a, tv 2 3 (by decide) a ∈ Γ := fun a => by
    have h1 := comm20_03 a 1
    rw [mul_one] at h1
    have : tv 2 3 (by decide) a = tv 2 0 (by decide) a * tv 0 3 (by decide) 1 * (tv 0 3 (by decide) 1 * tv 2 0 (by decide) a)⁻¹ := by
      rw [h1]; group
    rw [this]
    exact Γ.mul_mem (Γ.mul_mem (t20 a) (t03 1)) (Γ.inv_mem (Γ.mul_mem (t03 1) (t20 a)))
  have t32 : ∀ a, tv 3 2 (by decide) a ∈ Γ := fun a => by
    have h1 := comm30_02 a 1
    rw [mul_one] at h1
    have : tv 3 2 (by decide) a = tv 3 0 (by decide) a * tv 0 2 (by decide) 1 * (tv 0 2 (by decide) 1 * tv 3 0 (by decide) a)⁻¹ := by
      rw [h1]; group
    rw [this]
    exact Γ.mul_mem (Γ.mul_mem (t30 a) (t02 1)) (Γ.inv_mem (Γ.mul_mem (t02 1) (t30 a)))
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 4) (K := F)]
  refine (Subgroup.closure_le Γ).2 ?_
  rintro _ ⟨i, j, hij, c, rfl⟩
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact h01 c | exact h10 c | exact t21 c | exact t12 c | exact t20 c | exact t02 c
    | exact t30 c | exact t03 c | exact t31 c | exact t13 c | exact t23 c | exact t32 c

theorem mix_E (Γ : Subgroup SL(4, F)) (h01 : ∀ a, tv 0 1 (by decide) a ∈ Γ) (h10 : ∀ a, tv 1 0 (by decide) a ∈ Γ)
    (α0 α1 β0 β1 γ0 γ1 δ0 δ1 : F) (hu : α0 * δ0 - α1 * δ1 - β0 * γ0 + β1 * γ1 = 1)
    (hv : α0 * δ1 + α1 * δ0 - β0 * γ1 - β1 * γ0 = 0) (hr : rEsl α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv ∈ Γ)
    (hm : α0 * δ1 + α1 * δ0 ≠ 0)
    (hN1 : (γ0 * α0 + γ1 * α1) * (γ0 * α0 + γ1 * α1) + (γ1 * α0 - γ0 * α1) * (γ1 * α0 - γ0 * α1) ≠ 0)
    (hN2 : (δ0 * β1 - δ1 * β0) * (δ0 * β1 - δ1 * β0) + (δ0 * β0 + δ1 * β1) * (δ0 * β0 + δ1 * β1) ≠ 0) :
    Γ = ⊤ := by
  have hG := planar_mem_of_elem Γ h01 h10
  have hw : (wH : SL(4, F)) ∈ Γ := by
    rw [wH_eq]; exact Γ.mul_mem (Γ.mul_mem (h01 _) (h10 _)) (h01 _)
  have A := Qminus_roots Γ hG hw α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv hr hm hN1
  have B := Q_roots Γ hG hw α0 α1 β0 β1 γ0 γ1 δ0 δ1 hu hv hr hm hN2
  exact top_of_roots Γ h01 h10 (fun a => (A a).1) (fun a => (A a).2.1) (fun a => (A a).2.2.1)
    (fun a => (A a).2.2.2) (fun a => (B a).1) (fun a => (B a).2.1) (fun a => (B a).2.2.1) (fun a => (B a).2.2.2)

end WeylSpan

end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
