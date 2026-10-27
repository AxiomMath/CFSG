module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang

public section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv

variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]

theorem isDomainImage_of_isPolynomialCurve {c : k → ModGL τ k} (hc : IsPolynomialCurve c) :
    SeminaireExp3.IsDomainImage k
      (SeminaireExp3.ZariskiGL.pt '' (modGLZariski τ k '' Set.range c)) := by
  obtain ⟨P, hP⟩ := hc
  have hz : ∀ (z : Polynomial k →ₐ[k] k) (f : Polynomial k), z f = f.eval (z Polynomial.X) := by
    intro z f
    rw [← Polynomial.coe_aeval_eq_eval, Polynomial.aeval_algHom_apply,
      Polynomial.aeval_X_left_apply]
  have hmat : ∀ z : Polynomial k →ₐ[k] k,
      endMatrix τ (c (z Polynomial.X) : Module.End k (RootModule τ k)) = z.mapMatrix P := fun z => by
    ext a b
    rw [hP, AlgHom.mapMatrix_apply, Matrix.map_apply, hz z (P a b)]
  have hdet : IsUnit P.det := by
    refine SeminaireExp3.isUnit_of_forall_algHom_ne_zero (k := k) fun z hzd => ?_
    have h := det_endMatrix_mul_inv (c (z Polynomial.X))
    rw [hmat z, ← AlgHom.map_det, hzd, zero_mul] at h
    exact zero_ne_one h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : GLCoord k (Label τ) →ₐ[k] Polynomial k,
      ψ = GLCoord.lift k (Label τ) P (↑hdet.unit⁻¹) hdet.mul_val_inv := ⟨_, rfl⟩
  have hpt : ∀ z : Polynomial k →ₐ[k] k,
      z.comp ψ = (modGLPoint τ k (c (z Polynomial.X))).ofConv := fun z => by
    refine GLCoord.algHom_ext_of_entries fun a b => ?_
    rw [AlgHom.comp_apply, hψ, GLCoord.lift_glEntry, modGLPoint_apply_glEntry, ← endMatrix_apply,
      hmat z, AlgHom.mapMatrix_apply, Matrix.map_apply]
  refine ⟨Polynomial k, inferInstance, inferInstance, inferInstance, inferInstance, ψ, ?_⟩
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨t, rfl⟩, rfl⟩, rfl⟩
    refine ⟨Polynomial.aeval t, ?_⟩
    change (Polynomial.aeval t).comp ψ = _
    rw [hpt, Polynomial.aeval_X]
    rfl
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨_, ⟨z Polynomial.X, rfl⟩, rfl⟩, (hpt z).symm⟩

end CFSG.LieType.AlgebraicGroups

end
