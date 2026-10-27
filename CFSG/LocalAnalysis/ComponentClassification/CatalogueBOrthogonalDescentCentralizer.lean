module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentRestriction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentScalarExtension

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalDescent

open CatalogueBLinearTwoDescent

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
variable [Module.Finite K V]
variable (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (h2 : (2 : K) ≠ 0)
variable (T : V ≃+ V) (hT : Function.Involutive T)
variable (hsemi : ∀ a x, T (a • x) = sigma a • T x)
variable (B : LinearMap.BilinForm K V) (hsym : B.IsSymm) (c : Kˣ)
variable (hform : ∀ x y, (c : K) * B (T x) (T y) = sigma ((c : K) * B x y))

include hsym in
theorem extendFixedEquiv_preserves_bilinear
    (f : TauCeti.QuadraticMap.orthogonalGroup (descendedQuadratic sigma T hsemi B c hform))
    (x y : V) :
    B (extendFixedEquiv sigma hsigma hne h2 T hT hsemi f.val x)
        (extendFixedEquiv sigma hsigma hne h2 T hT hsemi f.val y) = B x y := by
  obtain ⟨e, he⟩ := CatalogueBLinearDescent.exists_fixed_finrank_basis
    sigma hsigma hne h2 T hT hsemi
  have hf := (descendedQuadratic_isometry_iff sigma T hsemi B c hform hsym h2 f.val).mp f.property
  let g := extendFixedEquiv sigma hsigma hne h2 T hT hsemi f.val
  have hB : B.comp g.toLinearMap g.toLinearMap = B := by
    apply LinearMap.BilinForm.ext_basis e
    intro i j
    have h := congrArg (fun a : fixedSubfield K sigma => (a : K))
      (hf ⟨e i, he i⟩ ⟨e j, he j⟩)
    rw [descendedBilinear_apply, descendedBilinear_apply] at h
    change B (g (e i)) (g (e j)) = B (e i) (e j)
    rw [show g (e i) = (f.val ⟨e i, he i⟩ : V) from
      extendFixedEquiv_fixed sigma hsigma hne h2 T hT hsemi f.val ⟨e i, he i⟩,
      show g (e j) = (f.val ⟨e j, he j⟩ : V) from
      extendFixedEquiv_fixed sigma hsigma hne h2 T hT hsemi f.val ⟨e j, he j⟩]
    exact mul_left_cancel₀ (Units.ne_zero c) h
  exact congrArg (fun D : LinearMap.BilinForm K V => D x y) hB

@[expose] def orthogonalFixedExtension :
    TauCeti.QuadraticMap.orthogonalGroup (descendedQuadratic sigma T hsemi B c hform) →*
      semilinearOrthogonalCentralizer (originalQuadratic B) T where
  toFun f := ⟨⟨extendFixedEquiv sigma hsigma hne h2 T hT hsemi f.val,
    (originalQuadratic_isometry_iff B hsym h2 _).mpr
      (extendFixedEquiv_preserves_bilinear sigma hsigma hne h2 T hT hsemi B hsym c hform f)⟩,
    (mem_semilinearOrthogonalCentralizer_iff (originalQuadratic B) T _).mpr
      (extendFixedEquiv_commutes sigma hsigma hne h2 T hT hsemi f.val)⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact extendFixedEquiv_one sigma hsigma hne h2 T hT hsemi
  map_mul' f g := by
    apply Subtype.ext
    apply Subtype.ext
    exact extendFixedEquiv_mul sigma hsigma hne h2 T hT hsemi f.val g.val

theorem orthogonalFixedExtension_smul
    (f : TauCeti.QuadraticMap.orthogonalGroup (descendedQuadratic sigma T hsemi B c hform))
    (a : K) (w : fixedSubspace sigma T hsemi) :
    (orthogonalFixedExtension sigma hsigma hne h2 T hT hsemi B hsym c hform f).val.val
      (a • (w : V)) = a • (f.val w : V) :=
  extendFixedEquiv_smul sigma hsigma hne h2 T hT hsemi f.val a w

theorem orthogonalFixedExtension_fixed
    (f : TauCeti.QuadraticMap.orthogonalGroup (descendedQuadratic sigma T hsemi B c hform))
    (w : fixedSubspace sigma T hsemi) :
    (orthogonalFixedExtension sigma hsigma hne h2 T hT hsemi B hsym c hform f).val.val
      (w : V) = (f.val w : V) :=
  extendFixedEquiv_fixed sigma hsigma hne h2 T hT hsemi f.val w

theorem orthogonalFixedExtension_symm_smul
    (f : TauCeti.QuadraticMap.orthogonalGroup (descendedQuadratic sigma T hsemi B c hform))
    (a : K) (w : fixedSubspace sigma T hsemi) :
    (orthogonalFixedExtension sigma hsigma hne h2 T hT hsemi B hsym c hform f).val.val.symm
      (a • (w : V)) = a • (f.val.symm w : V) := by
  change (extendFixedEquiv sigma hsigma hne h2 T hT hsemi f.val).symm _ = _
  rw [extendFixedEquiv_symm]
  exact extendFixedEquiv_smul sigma hsigma hne h2 T hT hsemi f.val.symm a w

theorem orthogonalFixedRestriction_extension
    (f : TauCeti.QuadraticMap.orthogonalGroup (descendedQuadratic sigma T hsemi B c hform)) :
    orthogonalFixedRestriction sigma T hsemi B hsym h2 c hform
      (orthogonalFixedExtension sigma hsigma hne h2 T hT hsemi B hsym c hform f) = f := by
  apply Subtype.ext
  ext w
  exact orthogonalFixedExtension_fixed sigma hsigma hne h2 T hT hsemi B hsym c hform f w

theorem orthogonalFixedExtension_restriction
    (g : semilinearOrthogonalCentralizer (originalQuadratic B) T) :
    orthogonalFixedExtension sigma hsigma hne h2 T hT hsemi B hsym c hform
      (orthogonalFixedRestriction sigma T hsemi B hsym h2 c hform g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply linearMap_ext_fixed sigma hsigma hne h2 T hT hsemi
  intro w
  exact orthogonalFixedExtension_fixed sigma hsigma hne h2 T hT hsemi B hsym c hform
    (orthogonalFixedRestriction sigma T hsemi B hsym h2 c hform g) w

@[expose] def orthogonalFixedCentralizerEquiv :
    semilinearOrthogonalCentralizer (originalQuadratic B) T ≃*
      TauCeti.QuadraticMap.orthogonalGroup (descendedQuadratic sigma T hsemi B c hform) where
  toFun := orthogonalFixedRestriction sigma T hsemi B hsym h2 c hform
  invFun := orthogonalFixedExtension sigma hsigma hne h2 T hT hsemi B hsym c hform
  left_inv := orthogonalFixedExtension_restriction sigma hsigma hne h2 T hT hsemi B hsym c hform
  right_inv := orthogonalFixedRestriction_extension sigma hsigma hne h2 T hT hsemi B hsym c hform
  map_mul' := (orthogonalFixedRestriction sigma T hsemi B hsym h2 c hform).map_mul

theorem orthogonalFixedCentralizerEquiv_apply
    (g : semilinearOrthogonalCentralizer (originalQuadratic B) T)
    (w : fixedSubspace sigma T hsemi) :
    ((orthogonalFixedCentralizerEquiv sigma hsigma hne h2 T hT hsemi B hsym c hform g).val w : V) =
      g.val.val (w : V) := rfl

theorem orthogonalFixedCentralizerEquiv_symm_smul
    (f : TauCeti.QuadraticMap.orthogonalGroup (descendedQuadratic sigma T hsemi B c hform))
    (a : K) (w : fixedSubspace sigma T hsemi) :
    ((orthogonalFixedCentralizerEquiv sigma hsigma hne h2 T hT hsemi B hsym c hform).symm f).val.val
      (a • (w : V)) = a • (f.val w : V) :=
  orthogonalFixedExtension_smul sigma hsigma hne h2 T hT hsemi B hsym c hform f a w

end CFSG.ComponentClassification.CatalogueBOrthogonalDescent
