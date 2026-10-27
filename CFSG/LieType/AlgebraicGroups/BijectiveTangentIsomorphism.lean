module

public import CFSG.LieType.AlgebraicGroups.BijectiveTangentDescent
public import CFSG.LieType.AlgebraicGroups.TwistedOrbitSurjectivity

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open Coalgebra Bialgebra HopfAlgebra WithConv

namespace BijectiveTangent

variable {k : Type} [Field k] {R B : Type} [CommRing R] [HopfAlgebra k R] [CommRing B]
  [HopfAlgebra k B]

theorem biTransCo_comp_bialgHom (φ : R →ₐc[k] B) (a b : WithConv (B →ₐ[k] k)) :
    (biTransCo a b).comp (φ : R →ₐ[k] B) =
      (φ : R →ₐ[k] B).comp (biTransCo (toConv (a.ofConv.comp (φ : R →ₐ[k] B)))
        (toConv (b.ofConv.comp (φ : R →ₐ[k] B)))) := by
  unfold biTransCo
  rw [AlgHom.convMul_comp_bialgHom_distrib, toConv_ofConv, AlgHom.convMul_comp_bialgHom_distrib,
    toConv_ofConv, AlgHom.comp_convMul_distrib, toConv_ofConv, AlgHom.comp_convMul_distrib,
    toConv_ofConv, comp_constPoint, comp_constPoint, ofConv_toConv, ofConv_toConv,
    AlgHom.id_comp, AlgHom.comp_id]
  rfl

theorem bijective_tangentMap_of_bijective_tangentMap_counit (φ : R →ₐc[k] B)
    (htan : Function.Bijective (tangentMap (φ : R →ₐ[k] B) (BialgHom.counitAlgHom_comp φ)))
    (x : B →ₐ[k] k) :
    Function.Bijective (tangentMap (φ : R →ₐ[k] B) (rfl : x.comp (φ : R →ₐ[k] B) = x.comp φ)) := by
  have h₁ : Function.Bijective (tangentMap (φ : R →ₐ[k] B)
      (rfl : (counitAlgHom k B).comp (φ : R →ₐ[k] B) = (counitAlgHom k B).comp φ)) := by
    have he : (counitAlgHom k R).comp (AlgHom.id k R) = (counitAlgHom k B).comp φ := by
      rw [AlgHom.comp_id, BialgHom.counitAlgHom_comp]
    have hid := tangentMap_bijective_of_comp_eq_id (AlgHom.id k R) (AlgHom.id k R)
      (AlgHom.comp_id _) (AlgHom.comp_id _) he
    have hfac : ⇑(tangentMap (φ : R →ₐ[k] B)
        (rfl : (counitAlgHom k B).comp (φ : R →ₐ[k] B) = (counitAlgHom k B).comp φ)) =
        ⇑(tangentMap (AlgHom.id k R) he) ∘
          ⇑(tangentMap (φ : R →ₐ[k] B) (BialgHom.counitAlgHom_comp φ)) := by
      funext D
      exact Subtype.ext (LinearMap.ext fun _ => rfl)
    rw [hfac]
    exact hid.comp htan
  have hx : (counitAlgHom k B).comp (biTransCo (toConv x) 1) = x := by
    rw [counit_comp_biTransCo, mul_one]
  exact tangentMap_bijective_of_comp_eq (φ : R →ₐ[k] B) (biTransCo_comp_inv _ _)
    (biTransCo_inv_comp _ _) (biTransCo_comp_inv _ _) (biTransCo_inv_comp _ _)
    (biTransCo_comp_bialgHom φ (toConv x) 1) hx h₁

end BijectiveTangent

theorem exceptional_Lang_bijective_tangent_group_map_isomorphism {k : Type} [Field k]
    [IsAlgClosed k] {R B : Type} [CommRing R] [HopfAlgebra k R] [Algebra.FiniteType k R]
    [Algebra.Smooth k R] [CommRing B] [HopfAlgebra k B] [Algebra.FiniteType k B]
    [Algebra.Smooth k B] (φ : R →ₐc[k] B)
    (hpt : Function.Bijective fun h : WithConv (B →ₐ[k] k) =>
      toConv (h.ofConv.comp (φ : R →ₐ[k] B)))
    (htan : Function.Bijective (tangentMap (φ : R →ₐ[k] B) (BialgHom.counitAlgHom_comp φ))) :
    ∃ ψ : B →ₐc[k] R, ψ.comp φ = BialgHom.id k R ∧ φ.comp ψ = BialgHom.id k B := by
  obtain ⟨hét, hopen, -⟩ := (exceptional_Lang_smooth_tangent_isomorphism_open
    (φ : R →ₐ[k] B)).2
    (BijectiveTangent.bijective_tangentMap_of_bijective_tangentMap_counit φ htan)
  let : Algebra R B := ((φ : R →ₐ[k] B) : R →+* B).toAlgebra
  have : IsScalarTower k R B := .of_algebraMap_eq fun c => ((φ : R →ₐ[k] B).commutes c).symm
  have : Algebra.Etale R B := hét
  have hsurj : ∀ y : R →ₐ[k] k, ∃ x : B →ₐ[k] k, x.comp (φ : R →ₐ[k] B) = y := fun y => by
    obtain ⟨h, hh⟩ := hpt.2 (toConv y)
    exact ⟨h.ofConv, congrArg ofConv hh⟩
  have : Module.FaithfullyFlat R B := Module.FaithfullyFlat.of_comap_surjective
    (BijectiveTangent.surjective_comap_of_isOpenMap (φ : R →ₐ[k] B) hopen hsurj)
  have hinj : Function.Injective fun x : B →ₐ[k] k => x.comp (IsScalarTower.toAlgHom k R B) := by
    intro x₁ x₂ h
    have h' : toConv (x₁.comp (φ : R →ₐ[k] B)) = toConv (x₂.comp (φ : R →ₐ[k] B)) :=
      congrArg toConv (AlgHom.ext fun r => DFunLike.congr_fun h r)
    exact congrArg ofConv (hpt.1 h')
  have hbij : Function.Bijective φ := BijectiveTangent.bijective_algebraMap_of_injective_lmul'
    (BijectiveTangent.injective_lmul'_of_injective_comp hinj)
  let e := BialgEquiv.ofBijective φ hbij
  have he : ∀ r, e r = φ r := fun r => congrFun (BialgEquiv.coe_ofBijective φ hbij) r
  refine ⟨(e.symm : B →ₐc[k] R), ?_, ?_⟩
  · ext r
    rw [BialgHom.comp_apply, BialgHom.id_apply, ← he]
    exact e.symm_apply_apply r
  · ext b
    rw [BialgHom.comp_apply, BialgHom.id_apply, ← he]
    exact e.apply_symm_apply b

end CFSG.LieType.AlgebraicGroups
