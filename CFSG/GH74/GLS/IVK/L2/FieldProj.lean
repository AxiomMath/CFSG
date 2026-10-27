module

public import CFSG.GH74.GLS.IVK.L2.Transport

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

section FieldProj

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] (e : K ≃* L2 F)

@[expose] noncomputable def thetaAut : MulAut K ≃* PGammaL2 F :=
  (MulAut.congr (toPSL e)).trans (semilinearEquivAut F).symm

theorem thetaAut_innDiagHom (g : PGL2 F) :
    thetaAut e (innDiagHom e g) = SemidirectProduct.inl g := by
  rw [innDiagHom_apply']
  show (semilinearEquivAut F).symm ((MulAut.congr (toPSL e))
    ((MulAut.congr (toPSL e)).symm (pglAction F g))) = _
  rw [MulEquiv.apply_symm_apply, ← semilinearEquivAut_inl]
  exact MulEquiv.symm_apply_apply _ _

theorem thetaAut_fieldAutHom (σ : F ≃+* F) :
    thetaAut e (fieldAutHom e σ) = SemidirectProduct.inr σ := by
  rw [fieldAutHom_apply']
  show (semilinearEquivAut F).symm ((MulAut.congr (toPSL e))
    ((MulAut.congr (toPSL e)).symm (psl2FieldAut F σ))) = _
  rw [MulEquiv.apply_symm_apply, ← semilinearEquivAut_inr]
  exact MulEquiv.symm_apply_apply _ _

@[expose] noncomputable def fieldProj : MulAut K →* (F ≃+* F) :=
  SemidirectProduct.rightHom.comp (thetaAut e).toMonoidHom

theorem fieldProj_apply (x : MulAut K) : fieldProj e x = (thetaAut e x).right := rfl

theorem fieldProj_innDiagHom (g : PGL2 F) : fieldProj e (innDiagHom e g) = 1 := by
  rw [fieldProj_apply, thetaAut_innDiagHom]
  simp

theorem fieldProj_fieldAutHom (σ : F ≃+* F) : fieldProj e (fieldAutHom e σ) = σ := by
  rw [fieldProj_apply, thetaAut_fieldAutHom]
  simp

theorem mem_innDiagSub_iff (x : MulAut K) : x ∈ innDiagSub e ↔ fieldProj e x = 1 := by
  constructor
  · rintro ⟨g, rfl⟩
    exact fieldProj_innDiagHom e g
  · intro h
    refine ⟨(thetaAut e x).left, ?_⟩
    apply (thetaAut e).injective
    rw [thetaAut_innDiagHom]
    have h1 : (thetaAut e x).right = 1 := h
    apply SemidirectProduct.ext
    · simp
    · simp [h1]

theorem mem_fieldAutSub_iff (x : MulAut K) : x ∈ fieldAutSub e ↔ (thetaAut e x).left = 1 := by
  constructor
  · rintro ⟨σ, rfl⟩
    rw [thetaAut_fieldAutHom]
    simp
  · intro h
    refine ⟨(thetaAut e x).right, ?_⟩
    apply (thetaAut e).injective
    rw [thetaAut_fieldAutHom]
    apply SemidirectProduct.ext
    · simp [h]
    · simp

theorem fieldAutHom_fieldProj_mul (x : MulAut K) :
    ∃ g ∈ innDiagSub e, x = g * fieldAutHom e (fieldProj e x) := by
  refine ⟨x * (fieldAutHom e (fieldProj e x))⁻¹, ?_, by simp⟩
  rw [mem_innDiagSub_iff, map_mul, map_inv, fieldProj_fieldAutHom]
  simp

end FieldProj

end CFSG.GH74.GLS.IVK
