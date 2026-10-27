module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBFieldConjugation

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticB

open CatalogueBLinearTwoDescent CatalogueBOrthogonalDescent CatalogueBAlternatingIsometry

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

section Form

variable (sigma : K ≃+* K) (T : V ≃+ V) (hsemi : ∀ a x, T (a • x) = sigma a • T x)
variable (B : LinearMap.BilinForm K V) (c : Kˣ)
variable (hform : ∀ x y, (c : K) * B (T x) (T y) = sigma ((c : K) * B x y))

theorem descendedBilinear_isAlt (hB : B.IsAlt) :
    (descendedBilinear sigma T hsemi B c hform).IsAlt := by
  intro x
  apply Subtype.ext
  rw [descendedBilinear_apply, hB (x : V), mul_zero]
  rfl

include hform in
theorem descendedBilinear_nondegenerate_of_isAlt [Module.Finite K V]
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (h2 : (2 : K) ≠ 0)
    (hT : Function.Involutive T) (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    (descendedBilinear sigma T hsemi B c hform).Nondegenerate := by
  have hleft : (descendedBilinear sigma T hsemi B c hform).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    change (x : V) = 0
    apply hnd.1
    obtain ⟨e, he⟩ := CatalogueBLinearDescent.exists_fixed_finrank_basis
      sigma hsigma hne h2 T hT hsemi
    have hzero (i : Fin (Module.finrank K V)) : B (x : V) (e i) = 0 := by
      have h := congrArg (fun a : fixedSubfield K sigma => (a : K)) (hx ⟨e i, he i⟩)
      rw [descendedBilinear_apply] at h
      exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero c)
    have hmap : B (x : V) = 0 := by
      apply e.ext
      intro i
      exact hzero i
    intro y
    rw [hmap]
    rfl
  refine ⟨hleft, fun y hy => hleft y fun x => ?_⟩
  rw [← LinearMap.IsAlt.neg (descendedBilinear_isAlt sigma T hsemi B c hform hB) x y, hy x,
    neg_zero]

end Form

section Centralizer

variable (sigma : K ≃+* K) (T : V ≃+ V) (hsemi : ∀ a x, T (a • x) = sigma a • T x)

theorem symplecticCentralizer_preserves_fixed (B : LinearMap.BilinForm K V)
    (g : semilinearSymplecticCentralizer B T) (x : fixedSubspace sigma T hsemi) :
    g.val.val (x : V) ∈ fixedSubspace sigma T hsemi := by
  change T (g.val.val (x : V)) = g.val.val (x : V)
  rw [← semilinearSymplecticCentralizer_commutes, x.property]

@[expose] def symplecticCentralizerFixedEquiv (B : LinearMap.BilinForm K V)
    (g : semilinearSymplecticCentralizer B T) :
    (fixedSubspace sigma T hsemi) ≃ₗ[fixedSubfield K sigma] (fixedSubspace sigma T hsemi) where
  toFun x := ⟨g.val.val (x : V), symplecticCentralizer_preserves_fixed sigma T hsemi B g x⟩
  invFun x := ⟨g.val.val.symm (x : V),
    symplecticCentralizer_preserves_fixed sigma T hsemi B g⁻¹ x⟩
  left_inv x := Subtype.ext (g.val.val.symm_apply_apply (x : V))
  right_inv x := Subtype.ext (g.val.val.apply_symm_apply (x : V))
  map_add' x y := Subtype.ext (map_add g.val.val (x : V) (y : V))
  map_smul' a x := Subtype.ext (map_smul g.val.val (a : K) (x : V))

theorem symplecticCentralizerFixedEquiv_apply (B : LinearMap.BilinForm K V)
    (g : semilinearSymplecticCentralizer B T) (x : fixedSubspace sigma T hsemi) :
    (symplecticCentralizerFixedEquiv sigma T hsemi B g x : V) = g.val.val (x : V) := rfl

theorem symplecticCentralizerFixedEquiv_symm_apply (B : LinearMap.BilinForm K V)
    (g : semilinearSymplecticCentralizer B T) (x : fixedSubspace sigma T hsemi) :
    ((symplecticCentralizerFixedEquiv sigma T hsemi B g).symm x : V) =
      g.val.val.symm (x : V) := rfl

variable (B : LinearMap.BilinForm K V) (c : Kˣ)
variable (hform : ∀ x y, (c : K) * B (T x) (T y) = sigma ((c : K) * B x y))

@[expose] def symplecticFixedRestriction :
    semilinearSymplecticCentralizer B T →*
      isometryGroup (descendedBilinear sigma T hsemi B c hform) where
  toFun g := ⟨symplecticCentralizerFixedEquiv sigma T hsemi B g, by
    apply (mem_isometryGroup_iff _ _).mpr
    intro x y
    apply Subtype.ext
    rw [descendedBilinear_apply, descendedBilinear_apply, symplecticCentralizerFixedEquiv_apply,
      symplecticCentralizerFixedEquiv_apply,
      (mem_isometryGroup_iff B g.val.val).mp g.val.property]⟩
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

theorem symplecticFixedRestriction_apply (g : semilinearSymplecticCentralizer B T)
    (x : fixedSubspace sigma T hsemi) :
    ((symplecticFixedRestriction sigma T hsemi B c hform g).val x : V) = g.val.val (x : V) :=
  rfl

theorem symplecticFixedRestriction_symm_apply (g : semilinearSymplecticCentralizer B T)
    (x : fixedSubspace sigma T hsemi) :
    (((symplecticFixedRestriction sigma T hsemi B c hform g).val).symm x : V) =
      g.val.val.symm (x : V) := rfl

variable [Module.Finite K V]
variable (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (h2 : (2 : K) ≠ 0)
variable (hT : Function.Involutive T)

theorem extendFixedEquiv_preserves_form
    (f : isometryGroup (descendedBilinear sigma T hsemi B c hform)) (x y : V) :
    B (extendFixedEquiv sigma hsigma hne h2 T hT hsemi f.val x)
        (extendFixedEquiv sigma hsigma hne h2 T hT hsemi f.val y) = B x y := by
  obtain ⟨e, he⟩ := CatalogueBLinearDescent.exists_fixed_finrank_basis
    sigma hsigma hne h2 T hT hsemi
  have hf := (mem_isometryGroup_iff _ f.val).mp f.property
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

@[expose] def symplecticFixedExtension :
    isometryGroup (descendedBilinear sigma T hsemi B c hform) →*
      semilinearSymplecticCentralizer B T where
  toFun f := ⟨⟨extendFixedEquiv sigma hsigma hne h2 T hT hsemi f.val,
    (mem_isometryGroup_iff B _).mpr
      (extendFixedEquiv_preserves_form sigma T hsemi B c hform hsigma hne h2 hT f)⟩,
    (mem_semilinearSymplecticCentralizer_iff B T _).mpr
      (extendFixedEquiv_commutes sigma hsigma hne h2 T hT hsemi f.val)⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact extendFixedEquiv_one sigma hsigma hne h2 T hT hsemi
  map_mul' f g := by
    apply Subtype.ext
    apply Subtype.ext
    exact extendFixedEquiv_mul sigma hsigma hne h2 T hT hsemi f.val g.val

theorem symplecticFixedExtension_smul
    (f : isometryGroup (descendedBilinear sigma T hsemi B c hform))
    (a : K) (w : fixedSubspace sigma T hsemi) :
    (symplecticFixedExtension sigma T hsemi B c hform hsigma hne h2 hT f).val.val
      (a • (w : V)) = a • (f.val w : V) :=
  extendFixedEquiv_smul sigma hsigma hne h2 T hT hsemi f.val a w

theorem symplecticFixedExtension_symm_smul
    (f : isometryGroup (descendedBilinear sigma T hsemi B c hform))
    (a : K) (w : fixedSubspace sigma T hsemi) :
    (symplecticFixedExtension sigma T hsemi B c hform hsigma hne h2 hT f).val.val.symm
      (a • (w : V)) = a • (f.val.symm w : V) := by
  change (extendFixedEquiv sigma hsigma hne h2 T hT hsemi f.val).symm _ = _
  rw [extendFixedEquiv_symm]
  exact extendFixedEquiv_smul sigma hsigma hne h2 T hT hsemi f.val.symm a w

theorem symplecticFixedRestriction_extension
    (f : isometryGroup (descendedBilinear sigma T hsemi B c hform)) :
    symplecticFixedRestriction sigma T hsemi B c hform
      (symplecticFixedExtension sigma T hsemi B c hform hsigma hne h2 hT f) = f := by
  apply Subtype.ext
  ext w
  exact extendFixedEquiv_fixed sigma hsigma hne h2 T hT hsemi f.val w

theorem symplecticFixedExtension_restriction (g : semilinearSymplecticCentralizer B T) :
    symplecticFixedExtension sigma T hsemi B c hform hsigma hne h2 hT
      (symplecticFixedRestriction sigma T hsemi B c hform g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply linearMap_ext_fixed sigma hsigma hne h2 T hT hsemi
  intro w
  exact extendFixedEquiv_fixed sigma hsigma hne h2 T hT hsemi
    (symplecticFixedRestriction sigma T hsemi B c hform g).val w

@[expose] def symplecticFixedCentralizerEquiv :
    semilinearSymplecticCentralizer B T ≃*
      isometryGroup (descendedBilinear sigma T hsemi B c hform) where
  toFun := symplecticFixedRestriction sigma T hsemi B c hform
  invFun := symplecticFixedExtension sigma T hsemi B c hform hsigma hne h2 hT
  left_inv := symplecticFixedExtension_restriction sigma T hsemi B c hform hsigma hne h2 hT
  right_inv := symplecticFixedRestriction_extension sigma T hsemi B c hform hsigma hne h2 hT
  map_mul' := (symplecticFixedRestriction sigma T hsemi B c hform).map_mul

theorem symplecticFixedCentralizerEquiv_apply (g : semilinearSymplecticCentralizer B T)
    (w : fixedSubspace sigma T hsemi) :
    ((symplecticFixedCentralizerEquiv sigma T hsemi B c hform hsigma hne h2 hT g).val w : V) =
      g.val.val (w : V) := rfl

theorem symplecticFixedCentralizerEquiv_symm_smul
    (f : isometryGroup (descendedBilinear sigma T hsemi B c hform))
    (a : K) (w : fixedSubspace sigma T hsemi) :
    ((symplecticFixedCentralizerEquiv sigma T hsemi B c hform hsigma hne h2 hT).symm f).val.val
      (a • (w : V)) = a • (f.val w : V) :=
  symplecticFixedExtension_smul sigma T hsemi B c hform hsigma hne h2 hT f a w

end Centralizer

end CFSG.ComponentClassification.CatalogueBSymplecticB
