module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullIdentification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullProduct
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorLocal
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFchapter1section1 CFSG.BenderSuzuki.PFAppendixIII

universe u v w

variable {G : Type u} [Group G] [Finite G]
variable {F : Type v} [Group F] [Finite F] {Ξ : Type w} [MulAction F Ξ]

theorem full_original_hull_conjugation
    (H : Subgroup G) (z x g t : G) (a : pointRightCosetSpace H)
    (hfull : elementFixedSet H x = numeratorRightOrbit H (localInvolutionPointHull z x) a)
    (hP : fusionStronglyEmbedded
      ((rightCosetStabilizer H a).subgroupOf (localInvolutionPointHull z x)))
    (hI : ∀ y ∈ localInvolutionPointHull z x, orderOf y = 2 → y ∈ involutionPointClass z)
    (hodd : oddCore (localInvolutionPointHull z x) = ⊥)
    (ht : t ∈ involutionPointClass z) (htv : Commute t (rightConjugateElem x g))
    (e : localInvolutionPointHull z x ≃* F)
    (hrank : TwoRankAtLeastTwo F) (hdouble : MulAction.IsMultiplyPretransitive F Ξ 2)
    (b : Ξ) (hB : fusionStronglyEmbedded (MulAction.stabilizer F b)) :
    (MulAut.conj g⁻¹) '' involutionPointClass z = involutionPointClass z ∧
    (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
      Subgroup.centralizer ({rightConjugateElem x g} : Set G) ∧
    (localInvolutionPointHull z x).map (MulAut.conj g⁻¹).toMonoidHom =
      localInvolutionPointHull z (rightConjugateElem x g) ∧
    (∀ y : localInvolutionPointHull z x,
      (localHullConjugateEquiv z x g y : G) = g⁻¹ * y.val * g) ∧
    ((localInvolutionPointHull z (rightConjugateElem x g)).subgroupOf
      (Subgroup.centralizer ({rightConjugateElem x g} : Set G))).Normal ∧
    t ∈ localInvolutionPointHull z (rightConjugateElem x g) ∧
    (∀ y ∈ localInvolutionPointHull z (rightConjugateElem x g), orderOf y = 2 →
      y ∈ involutionPointClass z) ∧
    oddCore (localInvolutionPointHull z (rightConjugateElem x g)) = ⊥ ∧
    elementFixedSet H (rightConjugateElem x g) =
      numeratorRightOrbit H (localInvolutionPointHull z (rightConjugateElem x g))
        (pointRightCosetMul H a g) ∧
    (∀ y : elementFixedSet H x,
      (elementFixedSetConjugateEquiv H x g y).val = pointRightCosetMul H y.val g) ∧
    (∀ y : elementFixedSet H (rightConjugateElem x g),
      ((elementFixedSetConjugateEquiv H x g).symm y).val =
        pointRightCosetMul H y.val g⁻¹) ∧
    (letI := hullFixedSetAction H z x
     letI := hullFixedSetAction H z (rightConjugateElem x g)
     ∃ (E : localInvolutionPointHull z x ≃* F) (f : elementFixedSet H x ≃ Ξ),
       (∀ (l : localInvolutionPointHull z x) (y : elementFixedSet H x),
         f (l • y) = E l • f y) ∧
       (∀ (l : localInvolutionPointHull z (rightConjugateElem x g))
         (y : elementFixedSet H (rightConjugateElem x g)),
         conjugateFixedSetModelEquiv H x g f (l • y) =
           conjugateHullModelEquiv z x g E l • conjugateFixedSetModelEquiv H x g f y) ∧
       (∀ y : elementFixedSet H x, y.val = a →
         conjugateFixedSetModelEquiv H x g f (elementFixedSetConjugateEquiv H x g y) = b) ∧
       MulAction.IsPretransitive (localInvolutionPointHull z (rightConjugateElem x g))
         (elementFixedSet H (rightConjugateElem x g)) ∧
       MulAction.IsMultiplyPretransitive (localInvolutionPointHull z (rightConjugateElem x g))
         (elementFixedSet H (rightConjugateElem x g)) 2) := by
  have htrans : MulAction.IsPretransitive F Ξ := by
    let := hdouble
    exact MulAction.isPretransitive_of_is_two_pretransitive
  refine ⟨point_class_conjugate_image z g, centralizer_conjugate_map x g,
    local_hull_conjugate_map z x g, localHullConjugateEquiv_apply z x g,
    conjugate_hull_normal z x g, distinguished_mem_conjugate_hull ht htv,
    conjugate_hull_involutions_in_point_class z x g hI,
    conjugate_hull_oddCore_eq_bot z x g hodd,
    conjugate_hull_full_fixedSet_orbit H z x g a hfull,
    elementFixedSetConjugateEquiv_apply H x g,
    elementFixedSetConjugateEquiv_symm_apply H x g, ?_⟩
  let := hullFixedSetAction H z x
  let := hullFixedSetAction H z (rightConjugateElem x g)
  obtain ⟨E, f, hsource, hequiv, hbase, hpre⟩ :=
    conjugate_full_fixedSet_model_of_abstract_isomorphism H z x g a hfull hP
      hrank htrans b hB e
  exact ⟨E, f, hsource, hequiv, hbase, hpre,
    conjugate_model_doubly_transitive H z x g E f hsource hdouble⟩

theorem original_pair_product_hull_conjugation
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (x t : G) (hx : orderOf x = 2) (hxz : Commute x z) (hxt : Commute x t)
    (ht : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H (rightCosetMk H 1) t = beta)
    (hfull : elementFixedSet H x =
      numeratorRightOrbit H (localInvolutionPointHull z x) (rightCosetMk H 1))
    (hI : ∀ y ∈ localInvolutionPointHull z x, orderOf y = 2 → y ∈ involutionPointClass z)
    (hodd : oddCore (localInvolutionPointHull z x) = ⊥)
    (hzt : ∃ l ∈ localInvolutionPointHull z x, rightConjugateElem z l = t)
    (hxzclass : x * z ∈ involutionPointClass x)
    (e : localInvolutionPointHull z x ≃* F)
    (hrank : TwoRankAtLeastTwo F) (hdouble : MulAction.IsMultiplyPretransitive F Ξ 2)
    (b : Ξ) (hB : fusionStronglyEmbedded (MulAction.stabilizer F b)) :
    x * t ∈ involutionPointClass x ∧
    ∃ g : G, rightConjugateElem x g = x * t ∧
      (localInvolutionPointHull z x).map (MulAut.conj g⁻¹).toMonoidHom =
        localInvolutionPointHull z (x * t) ∧
      ((localInvolutionPointHull z (x * t)).subgroupOf
        (Subgroup.centralizer ({x * t} : Set G))).Normal ∧
      t ∈ localInvolutionPointHull z (x * t) ∧
      (∀ y ∈ localInvolutionPointHull z (x * t), orderOf y = 2 → y ∈ involutionPointClass z) ∧
      oddCore (localInvolutionPointHull z (x * t)) = ⊥ ∧
      elementFixedSet H (x * t) =
        numeratorRightOrbit H (localInvolutionPointHull z (x * t))
          (pointRightCosetMul H (rightCosetMk H 1) g) ∧
      (letI := hullFixedSetAction H z (x * t)
       ∃ (E : localInvolutionPointHull z (x * t) ≃* F) (f : elementFixedSet H (x * t) ≃ Ξ),
         (∀ (l : localInvolutionPointHull z (x * t)) (y : elementFixedSet H (x * t)),
           f (l • y) = E l • f y) ∧
         MulAction.IsPretransitive (localInvolutionPointHull z (x * t)) (elementFixedSet H (x * t)) ∧
         MulAction.IsMultiplyPretransitive (localInvolutionPointHull z (x * t))
           (elementFixedSet H (x * t)) 2) := by
  have hprod := local_hull_product_in_original_class x z t hzt hxzclass
  obtain ⟨g, hg⟩ := local_hull_product_conjugator x z t hzt hxzclass
  have hPt := (original_pair_local_hull_inputs h beta hbeta x t hx hxz hxt ht hflip).2.2.2.2
  have hP : fusionStronglyEmbedded
      ((rightCosetStabilizer H (rightCosetMk H 1)).subgroupOf (localInvolutionPointHull z x)) := by
    rw [rightCosetStabilizer_base]
    exact hPt
  have htv : Commute t (rightConjugateElem x g) := by
    rw [hg]
    exact hxt.symm.mul_right (Commute.refl t)
  have hall := full_original_hull_conjugation H z x g t (rightCosetMk H 1)
    hfull hP hI hodd ht htv e hrank hdouble b hB
  rcases hall with ⟨_, _, hmap, _, hnormal, htL, hI₁, hodd₁, horbit, _, _, hmodel⟩
  have hactual :
      (letI := hullFixedSetAction H z (rightConjugateElem x g)
       ∃ (E : localInvolutionPointHull z (rightConjugateElem x g) ≃* F)
         (f : elementFixedSet H (rightConjugateElem x g) ≃ Ξ),
         (∀ (l : localInvolutionPointHull z (rightConjugateElem x g))
           (y : elementFixedSet H (rightConjugateElem x g)), f (l • y) = E l • f y) ∧
         MulAction.IsPretransitive (localInvolutionPointHull z (rightConjugateElem x g))
           (elementFixedSet H (rightConjugateElem x g)) ∧
         MulAction.IsMultiplyPretransitive (localInvolutionPointHull z (rightConjugateElem x g))
           (elementFixedSet H (rightConjugateElem x g)) 2) := by
    let := hullFixedSetAction H z (rightConjugateElem x g)
    obtain ⟨E, f, _, hequiv, _, hpre, htwo⟩ := hmodel
    exact ⟨conjugateHullModelEquiv z x g E, conjugateFixedSetModelEquiv H x g f,
      hequiv, hpre, htwo⟩
  refine ⟨hprod, g, hg, ?_⟩
  rw [hg] at hmap hnormal htL hI₁ hodd₁ horbit hactual
  exact ⟨hmap, hnormal, htL, hI₁, hodd₁, horbit, hactual⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
