module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFieldComponentBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

section Transport

variable {H C : Type*} [Group H] [Group C]

theorem mulAutHom_congr_eq_of_intertwine (F : MulAut H →* C)
    (hF : ∀ a b : MulAut H, F a * F b = F b * F a) {S₁ S₂ : Type*} [Group S₁] [Group S₂]
    (ι₁ : S₁ ≃* H) (ι₂ : S₂ ≃* H) (θ : S₁ ≃* S₂) (γ₁ : MulAut S₁) (γ₂ : MulAut S₂)
    (h : ∀ x, γ₂ (θ x) = θ (γ₁ x)) :
    F (MulAut.congr ι₁ γ₁) = F (MulAut.congr ι₂ γ₂) := by
  set ψ : MulAut H := ι₁.symm.trans (θ.trans ι₂) with hψ
  have key : MulAut.congr ι₂ γ₂ = ψ * MulAut.congr ι₁ γ₁ * ψ⁻¹ := by
    ext A
    simp only [MulAut.congr_apply, MulAut.mul_apply, hψ, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    rw [MulAut.inv_def, MulEquiv.symm_trans_apply, MulEquiv.symm_trans_apply,
      MulEquiv.symm_symm, MulEquiv.symm_apply_apply, ← h, MulEquiv.apply_symm_apply]
  rw [key, map_mul, map_mul, map_inv, hF ψ, mul_assoc, mul_inv_cancel, mul_one]

end Transport

section FieldPart

variable (K : Type*) [Field K]

@[expose] noncomputable def sl2DescendAut :
    MulAut (SpecialLinearGroup (Fin 2) K) →* MulAut (PSL2 K) where
  toFun α := QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) α
    (Subgroup.map_center_eq α)
  map_one' := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) x
    rfl
  map_mul' α β := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) x
    rfl

theorem sl2DescendAut_mk (α : MulAut (SpecialLinearGroup (Fin 2) K))
    (g : SpecialLinearGroup (Fin 2) K) :
    sl2DescendAut K α (QuotientGroup.mk' (Subgroup.center _) g) =
      QuotientGroup.mk' (Subgroup.center _) (α g) :=
  rfl

variable [Finite K]

@[expose] noncomputable def pGammaL2EquivAut : PGammaL2 K ≃* MulAut (PSL2 K) :=
  MulEquiv.ofBijective (semilinearAction K)
    ⟨semilinearAction_injective K, semilinearAction_surjective K⟩

@[expose] noncomputable def psl2FieldPart : MulAut (PSL2 K) →* (K ≃+* K) :=
  SemidirectProduct.rightHom.comp (pGammaL2EquivAut K).symm.toMonoidHom

@[expose] noncomputable def sl2FieldPart : MulAut (SpecialLinearGroup (Fin 2) K) →* (K ≃+* K) :=
  (psl2FieldPart K).comp (sl2DescendAut K)

theorem sl2FieldPart_apply (α : MulAut (SpecialLinearGroup (Fin 2) K)) :
    sl2FieldPart K α = psl2FieldPart K (sl2DescendAut K α) :=
  rfl

theorem psl2FieldPart_semilinearAction (x : PGammaL2 K) :
    psl2FieldPart K (semilinearAction K x) = x.right := by
  change ((pGammaL2EquivAut K).symm (pGammaL2EquivAut K x)).right = x.right
  rw [MulEquiv.symm_apply_apply]

theorem psl2FieldPart_psl2FieldAut (σ : K ≃+* K) : psl2FieldPart K (psl2FieldAut K σ) = σ := by
  rw [← semilinearAction_inr K σ, psl2FieldPart_semilinearAction]
  rfl

theorem psl2FieldPart_pglAction (g : PGL2 K) : psl2FieldPart K (pglAction K g) = 1 := by
  rw [← semilinearAction_inl K g, psl2FieldPart_semilinearAction]
  rfl

theorem psl2FieldPart_conj (x : PSL2 K) : psl2FieldPart K (MulAut.conj x) = 1 := by
  rw [← pglAction_toPGL, psl2FieldPart_pglAction]

theorem sl2FieldPart_mul_comm (a b : MulAut (SpecialLinearGroup (Fin 2) K)) :
    sl2FieldPart K a * sl2FieldPart K b = sl2FieldPart K b * sl2FieldPart K a :=
  ringEquiv_mul_comm _ _

theorem sl2FieldPart_conj (M : SpecialLinearGroup (Fin 2) K) :
    sl2FieldPart K (MulAut.conj M) = 1 := by
  have h : sl2DescendAut K (MulAut.conj M) =
      MulAut.conj (QuotientGroup.mk' (Subgroup.center _) M : PSL2 K) := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) x
    rw [sl2DescendAut_mk, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  rw [sl2FieldPart_apply, h, psl2FieldPart_conj]

theorem sl2FieldPart_slFieldAut (σ : K ≃+* K) :
    sl2FieldPart K (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
      (Fin 2) K σ) = σ := by
  have h : sl2DescendAut K (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
      (Fin 2) K σ) = psl2FieldAut K σ := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) x
    rw [sl2DescendAut_mk, psl2FieldAut_apply, psl2RingEquiv_mk]
    rfl
  rw [sl2FieldPart_apply, h, psl2FieldPart_psl2FieldAut]

theorem sl2FieldPart_slConjugation (A : GL (Fin 2) K) :
    sl2FieldPart K (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 2 K A)
      = 1 := by
  have h : sl2DescendAut K
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 2 K A) =
      pglAction K (Matrix.ProjGenLinGroup.mk A) := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) x
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [toPGL_pglAction, sl2DescendAut_mk]
    change Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk _) =
      _ * Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk _) * _
    rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul,
      map_mul, map_inv]
  rw [sl2FieldPart_apply, h, psl2FieldPart_pglAction]

end FieldPart

section Graph

variable (K : Type*) [Field K]

@[expose] def sl2Weyl : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; -1, 0], by simp [det_fin_two]⟩

theorem slGraphAut_two_eq_conj :
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 2 K =
      MulAut.conj (sl2Weyl K) := by
  ext g i j
  rw [MulAut.conj_apply]
  change (((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ) i j =
    (((sl2Weyl K * g * (sl2Weyl K)⁻¹ : SpecialLinearGroup (Fin 2) K)) :
      Matrix (Fin 2) (Fin 2) K) i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    transpose_apply]
  have hw : ((sl2Weyl K : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![0, 1; -1, 0] := rfl
  rw [hw, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

variable [Finite K]

theorem sl2FieldPart_slGraphAut :
    sl2FieldPart K (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 2 K) = 1 := by
  rw [slGraphAut_two_eq_conj, sl2FieldPart_conj]

end Graph

end CFSG.SeitzReduction.LinearPilot
