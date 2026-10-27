module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFieldComponentBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq)

variable {m : ℕ} {K : Type*} [Field K] [Finite K]

@[expose] noncomputable def slFieldPart (hm : 3 ≤ m) :
    MulAut (SpecialLinearGroup (Fin m) K) →* (K ≃+* K) :=
  (linearFieldPart K hm).comp (descendAut m K)

theorem slFieldPart_apply (hm : 3 ≤ m) (γ : MulAut (SpecialLinearGroup (Fin m) K)) :
    slFieldPart hm γ = linearFieldPart K hm (descendAut m K γ) :=
  rfl

theorem slFieldPart_slFieldAut (hm : 3 ≤ m) (σ : K ≃+* K) :
    slFieldPart hm (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
      (Fin m) K σ) = σ := by
  rw [slFieldPart_apply]
  exact linearFieldPart_fieldAut hm σ

theorem slFieldPart_slConjugation (hm : 3 ≤ m) (A : GL (Fin m) K) :
    slFieldPart hm (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
      m K A) = 1 := by
  rw [slFieldPart_apply]
  exact linearFieldPart_conjAut hm A

theorem slFieldPart_slGraphAut (hm : 3 ≤ m) :
    slFieldPart hm (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut m K) = 1 := by
  rw [slFieldPart_apply]
  exact linearFieldPart_dualAut hm

theorem slFieldPart_conj (hm : 3 ≤ m) (γ ψ : MulAut (SpecialLinearGroup (Fin m) K)) :
    slFieldPart hm (ψ * γ * ψ⁻¹) = slFieldPart hm γ := by
  rw [map_mul, map_mul, map_inv, ringEquiv_mul_comm (slFieldPart hm ψ), mul_assoc,
    mul_inv_cancel, mul_one]

theorem slFieldPart_eq_of_intertwine (hm : 3 ≤ m) {S₁ S₂ : Type*} [Group S₁] [Group S₂]
    (ι₁ : S₁ ≃* SpecialLinearGroup (Fin m) K) (ι₂ : S₂ ≃* SpecialLinearGroup (Fin m) K)
    (θ : S₁ ≃* S₂) (γ₁ : MulAut S₁) (γ₂ : MulAut S₂) (h : ∀ x, γ₂ (θ x) = θ (γ₁ x)) :
    slFieldPart hm (MulAut.congr ι₁ γ₁) = slFieldPart hm (MulAut.congr ι₂ γ₂) := by
  set ψ : MulAut (SpecialLinearGroup (Fin m) K) := ι₁.symm.trans (θ.trans ι₂) with hψ
  have key : MulAut.congr ι₂ γ₂ = ψ * MulAut.congr ι₁ γ₁ * ψ⁻¹ := by
    ext A
    simp only [MulAut.congr_apply, MulAut.mul_apply, hψ, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    rw [MulAut.inv_def, MulEquiv.symm_trans_apply, MulEquiv.symm_trans_apply,
      MulEquiv.symm_symm, MulEquiv.symm_apply_apply, ← h, MulEquiv.apply_symm_apply]
  rw [key, slFieldPart_conj]

end CFSG.SeitzReduction.LinearPilot
