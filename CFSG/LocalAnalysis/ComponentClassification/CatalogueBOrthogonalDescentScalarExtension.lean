module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentFixedSpace

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalDescent

open CatalogueBLinearTwoDescent
open scoped TensorProduct

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
variable [Module.Finite K V]
variable (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (h2 : (2 : K) ≠ 0)
variable (T : V ≃+ V) (hT : Function.Involutive T)
variable (hsemi : ∀ a x, T (a • x) = sigma a • T x)

@[expose] def scalarExtensionEquiv :
    (K ⊗[fixedSubfield K sigma] (fixedSubspace sigma T hsemi)) ≃ₗ[K] V :=
  Classical.choose (exists_scalarExtensionEquiv sigma hsigma hne h2 T hT hsemi)

theorem scalarExtensionEquiv_tmul (a : K) (x : fixedSubspace sigma T hsemi) :
    scalarExtensionEquiv sigma hsigma hne h2 T hT hsemi (a ⊗ₜ x) = a • (x : V) :=
  Classical.choose_spec (exists_scalarExtensionEquiv sigma hsigma hne h2 T hT hsemi) a x

theorem scalarExtensionEquiv_symm_smul (a : K) (x : fixedSubspace sigma T hsemi) :
    (scalarExtensionEquiv sigma hsigma hne h2 T hT hsemi).symm (a • (x : V)) = a ⊗ₜ x := by
  apply (scalarExtensionEquiv sigma hsigma hne h2 T hT hsemi).injective
  rw [LinearEquiv.apply_symm_apply, scalarExtensionEquiv_tmul]

theorem scalarExtensionEquiv_symm_fixed (x : fixedSubspace sigma T hsemi) :
    (scalarExtensionEquiv sigma hsigma hne h2 T hT hsemi).symm (x : V) = 1 ⊗ₜ x := by
  simpa only [one_smul] using scalarExtensionEquiv_symm_smul sigma hsigma hne h2 T hT hsemi 1 x

@[expose] def extendFixedEquiv
    (f : (fixedSubspace sigma T hsemi) ≃ₗ[fixedSubfield K sigma] (fixedSubspace sigma T hsemi)) :
    V ≃ₗ[K] V :=
  (scalarExtensionEquiv sigma hsigma hne h2 T hT hsemi).symm.trans
    ((LinearEquiv.baseChange (fixedSubfield K sigma) K _ _ f).trans
      (scalarExtensionEquiv sigma hsigma hne h2 T hT hsemi))

theorem extendFixedEquiv_smul
    (f : (fixedSubspace sigma T hsemi) ≃ₗ[fixedSubfield K sigma] (fixedSubspace sigma T hsemi))
    (a : K) (x : fixedSubspace sigma T hsemi) :
    extendFixedEquiv sigma hsigma hne h2 T hT hsemi f (a • (x : V)) = a • (f x : V) := by
  simp only [extendFixedEquiv, LinearEquiv.trans_apply, scalarExtensionEquiv_symm_smul,
    LinearEquiv.baseChange_tmul, scalarExtensionEquiv_tmul]

theorem extendFixedEquiv_fixed
    (f : (fixedSubspace sigma T hsemi) ≃ₗ[fixedSubfield K sigma] (fixedSubspace sigma T hsemi))
    (x : fixedSubspace sigma T hsemi) :
    extendFixedEquiv sigma hsigma hne h2 T hT hsemi f (x : V) = (f x : V) := by
  simpa only [one_smul] using extendFixedEquiv_smul sigma hsigma hne h2 T hT hsemi f 1 x

include hsigma hne h2 hT in
theorem linearMap_ext_fixed (g h : V →ₗ[K] V)
    (hfixed : ∀ x : fixedSubspace sigma T hsemi, g (x : V) = h (x : V)) : g = h := by
  obtain ⟨e, he⟩ := CatalogueBLinearDescent.exists_fixed_finrank_basis
    sigma hsigma hne h2 T hT hsemi
  apply e.ext
  intro i
  exact hfixed ⟨e i, he i⟩

theorem extendFixedEquiv_symm
    (f : (fixedSubspace sigma T hsemi) ≃ₗ[fixedSubfield K sigma] (fixedSubspace sigma T hsemi)) :
    (extendFixedEquiv sigma hsigma hne h2 T hT hsemi f).symm =
      extendFixedEquiv sigma hsigma hne h2 T hT hsemi f.symm := by
  ext x
  simp only [extendFixedEquiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.baseChange_symm, LinearEquiv.trans_apply]

theorem extendFixedEquiv_one :
    extendFixedEquiv sigma hsigma hne h2 T hT hsemi 1 = 1 := by
  apply LinearEquiv.toLinearMap_injective
  apply linearMap_ext_fixed sigma hsigma hne h2 T hT hsemi
  intro x
  exact extendFixedEquiv_fixed sigma hsigma hne h2 T hT hsemi 1 x

theorem extendFixedEquiv_mul
    (f g : (fixedSubspace sigma T hsemi) ≃ₗ[fixedSubfield K sigma] (fixedSubspace sigma T hsemi)) :
    extendFixedEquiv sigma hsigma hne h2 T hT hsemi (f * g) =
      extendFixedEquiv sigma hsigma hne h2 T hT hsemi f *
        extendFixedEquiv sigma hsigma hne h2 T hT hsemi g := by
  apply LinearEquiv.toLinearMap_injective
  apply linearMap_ext_fixed sigma hsigma hne h2 T hT hsemi
  intro x
  simp only [LinearEquiv.coe_coe, LinearEquiv.mul_apply, extendFixedEquiv_fixed]

theorem extendFixedEquiv_commutes
    (f : (fixedSubspace sigma T hsemi) ≃ₗ[fixedSubfield K sigma] (fixedSubspace sigma T hsemi))
    (x : V) :
    extendFixedEquiv sigma hsigma hne h2 T hT hsemi f (T x) =
      T (extendFixedEquiv sigma hsigma hne h2 T hT hsemi f x) := by
  obtain ⟨z, rfl⟩ := (scalarExtensionEquiv sigma hsigma hne h2 T hT hsemi).surjective x
  induction z using TensorProduct.inductionOn with
  | tmul a w =>
      rw [scalarExtensionEquiv_tmul, hsemi, w.property, extendFixedEquiv_smul,
        extendFixedEquiv_smul, hsemi, (f w).property]
  | add z z' hz hz' =>
      simp only [map_add, hz, hz']

end CFSG.ComponentClassification.CatalogueBOrthogonalDescent
