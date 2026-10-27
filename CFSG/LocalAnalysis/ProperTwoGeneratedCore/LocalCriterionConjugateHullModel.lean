module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullFixedSet

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.BenderSuzuki.PFAppendixIII

universe u v w

variable {G : Type u} [Group G]
variable {F : Type v} [Group F] {Ξ : Type w}

@[expose] def conjugateHullModelEquiv (z x g : G)
    (e : localInvolutionPointHull z x ≃* F) :
    localInvolutionPointHull z (rightConjugateElem x g) ≃* F :=
  (localHullConjugateEquiv z x g).symm.trans e

@[expose] def conjugateFixedSetModelEquiv (H : Subgroup G) (x g : G)
    (f : elementFixedSet H x ≃ Ξ) :
    elementFixedSet H (rightConjugateElem x g) ≃ Ξ :=
  (elementFixedSetConjugateEquiv H x g).symm.trans f

theorem conjugateHullModelEquiv_apply (z x g : G)
    (e : localInvolutionPointHull z x ≃* F)
    (l : localInvolutionPointHull z (rightConjugateElem x g)) :
    conjugateHullModelEquiv z x g e l = e ((localHullConjugateEquiv z x g).symm l) := rfl

theorem conjugateFixedSetModelEquiv_apply (H : Subgroup G) (x g : G)
    (f : elementFixedSet H x ≃ Ξ) (a : elementFixedSet H (rightConjugateElem x g)) :
    conjugateFixedSetModelEquiv H x g f a =
      f ((elementFixedSetConjugateEquiv H x g).symm a) := rfl

theorem conjugate_model_equivariant [MulAction F Ξ]
    (H : Subgroup G) (z x g : G)
    (e : localInvolutionPointHull z x ≃* F) (f : elementFixedSet H x ≃ Ξ)
    (hsource : letI := hullFixedSetAction H z x
      ∀ (l : localInvolutionPointHull z x) (a : elementFixedSet H x),
        f (l • a) = e l • f a) :
    letI := hullFixedSetAction H z (rightConjugateElem x g)
    ∀ (l : localInvolutionPointHull z (rightConjugateElem x g))
      (a : elementFixedSet H (rightConjugateElem x g)),
      conjugateFixedSetModelEquiv H x g f (l • a) =
        conjugateHullModelEquiv z x g e l • conjugateFixedSetModelEquiv H x g f a := by
  let := hullFixedSetAction H z x
  let := hullFixedSetAction H z (rightConjugateElem x g)
  intro l a
  let E := localHullConjugateEquiv z x g
  let B := elementFixedSetConjugateEquiv H x g
  have hbridge : B.symm (l • a) = E.symm l • B.symm a := by
    apply B.injective
    rw [B.apply_symm_apply]
    have hh := elementFixedSetConjugateEquiv_equivariant H z x g (E.symm l) (B.symm a)
    change B (E.symm l • B.symm a) = E (E.symm l) • B (B.symm a) at hh
    rw [E.apply_symm_apply, B.apply_symm_apply] at hh
    exact hh.symm
  change f (B.symm (l • a)) = e (E.symm l) • f (B.symm a)
  rw [hbridge]
  exact hsource (E.symm l) (B.symm a)

theorem conjugate_model_original_point (H : Subgroup G) (x g : G)
    (f : elementFixedSet H x ≃ Ξ) (a : elementFixedSet H x) :
    conjugateFixedSetModelEquiv H x g f (elementFixedSetConjugateEquiv H x g a) = f a := by
  rw [conjugateFixedSetModelEquiv_apply, Equiv.symm_apply_apply]

theorem conjugate_model_original_element (z x g : G)
    (e : localInvolutionPointHull z x ≃* F) (l : localInvolutionPointHull z x) :
    conjugateHullModelEquiv z x g e (localHullConjugateEquiv z x g l) = e l := by
  rw [conjugateHullModelEquiv_apply, MulEquiv.symm_apply_apply]

theorem conjugate_model_transitive [MulAction F Ξ]
    (H : Subgroup G) (z x g : G)
    (e : localInvolutionPointHull z x ≃* F) (f : elementFixedSet H x ≃ Ξ)
    (hsource : letI := hullFixedSetAction H z x
      ∀ (l : localInvolutionPointHull z x) (a : elementFixedSet H x), f (l • a) = e l • f a)
    (hmodel : MulAction.IsPretransitive F Ξ) :
    letI := hullFixedSetAction H z (rightConjugateElem x g)
    MulAction.IsPretransitive (localInvolutionPointHull z (rightConjugateElem x g))
      (elementFixedSet H (rightConjugateElem x g)) := by
  let := hullFixedSetAction H z (rightConjugateElem x g)
  let E := conjugateHullModelEquiv z x g e
  let B := conjugateFixedSetModelEquiv H x g f
  constructor
  intro a b
  obtain ⟨l, hl⟩ := hmodel.exists_smul_eq (B a) (B b)
  refine ⟨E.symm l, B.injective ?_⟩
  rw [conjugate_model_equivariant H z x g e f hsource, E.apply_symm_apply]
  exact hl

theorem conjugate_model_doubly_transitive [MulAction F Ξ]
    (H : Subgroup G) (z x g : G)
    (e : localInvolutionPointHull z x ≃* F) (f : elementFixedSet H x ≃ Ξ)
    (hsource : letI := hullFixedSetAction H z x
      ∀ (l : localInvolutionPointHull z x) (a : elementFixedSet H x), f (l • a) = e l • f a)
    (hmodel : MulAction.IsMultiplyPretransitive F Ξ 2) :
    letI := hullFixedSetAction H z (rightConjugateElem x g)
    MulAction.IsMultiplyPretransitive (localInvolutionPointHull z (rightConjugateElem x g))
      (elementFixedSet H (rightConjugateElem x g)) 2 := by
  let := hullFixedSetAction H z (rightConjugateElem x g)
  let E := conjugateHullModelEquiv z x g e
  let B := conjugateFixedSetModelEquiv H x g f
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨l, hla, hlb⟩ := MulAction.is_two_pretransitive_iff.mp hmodel
    (B.injective.ne hab) (B.injective.ne hcd)
  refine ⟨E.symm l, B.injective ?_, B.injective ?_⟩
  · rw [conjugate_model_equivariant H z x g e f hsource, E.apply_symm_apply]
    exact hla
  · rw [conjugate_model_equivariant H z x g e f hsource, E.apply_symm_apply]
    exact hlb

end CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
