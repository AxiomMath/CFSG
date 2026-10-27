module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorRightOrbit

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFchapter1section1 CFSG.BenderSuzuki.PFAppendixIII

universe u v w

variable {G : Type u} [Group G]

@[expose] def hullFixedSetOrbitEquiv (H : Subgroup G) (z x : G)
    (a : pointRightCosetSpace H)
    (hfull : elementFixedSet H x = numeratorRightOrbit H (localInvolutionPointHull z x) a) :
    elementFixedSet H x ≃ numeratorRightOrbit H (localInvolutionPointHull z x) a where
  toFun y := ⟨y.val, hfull ▸ y.property⟩
  invFun y := ⟨y.val, hfull.symm ▸ y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem hullFixedSetOrbitEquiv_equivariant (H : Subgroup G) (z x : G)
    (a : pointRightCosetSpace H)
    (hfull : elementFixedSet H x = numeratorRightOrbit H (localInvolutionPointHull z x) a) :
    letI := hullFixedSetAction H z x
    letI := numeratorRightOrbitAction H (localInvolutionPointHull z x) a
    ∀ (l : localInvolutionPointHull z x) (b : elementFixedSet H x),
      hullFixedSetOrbitEquiv H z x a hfull (l • b) =
        l • hullFixedSetOrbitEquiv H z x a hfull b := by
  let := hullFixedSetAction H z x
  let := numeratorRightOrbitAction H (localInvolutionPointHull z x) a
  intro l b
  apply Subtype.ext
  rfl

theorem original_full_fixedSet_model_of_abstract_isomorphism
    [Finite G] {F : Type v} [Group F] [Finite F] {Ξ : Type w} [MulAction F Ξ]
    (H : Subgroup G) (z x : G) (a : pointRightCosetSpace H)
    (hfull : elementFixedSet H x = numeratorRightOrbit H (localInvolutionPointHull z x) a)
    (hP : fusionStronglyEmbedded
      ((rightCosetStabilizer H a).subgroupOf (localInvolutionPointHull z x)))
    (hrank : TwoRankAtLeastTwo F) (htrans : MulAction.IsPretransitive F Ξ)
    (b : Ξ) (hB : fusionStronglyEmbedded (MulAction.stabilizer F b))
    (e : localInvolutionPointHull z x ≃* F) :
    letI := hullFixedSetAction H z x
    ∃ (E : localInvolutionPointHull z x ≃* F) (f : elementFixedSet H x ≃ Ξ),
      ((rightCosetStabilizer H a).subgroupOf (localInvolutionPointHull z x)).map
        E.toMonoidHom = MulAction.stabilizer F b ∧
      (∀ y : elementFixedSet H x, y.val = a → f y = b) ∧
      ∀ (l : localInvolutionPointHull z x) (y : elementFixedSet H x),
        f (l • y) = E l • f y := by
  let := hullFixedSetAction H z x
  let := numeratorRightOrbitAction H (localInvolutionPointHull z x) a
  obtain ⟨E, f₀, hE, hbase, hequiv⟩ := original_right_orbit_model_identification
    H (localInvolutionPointHull z x) a hP hrank htrans b hB e
  let B := hullFixedSetOrbitEquiv H z x a hfull
  let f := B.trans f₀
  refine ⟨E, f, hE, ?_, ?_⟩
  · intro y hy
    have hpoint : B y = ⟨a, numeratorRightOrbit_base H (localInvolutionPointHull z x) a⟩ :=
      Subtype.ext hy
    change f₀ (B y) = b
    rw [hpoint]
    exact hbase
  · intro l y
    change f₀ (B (l • y)) = E l • f₀ (B y)
    rw [hullFixedSetOrbitEquiv_equivariant H z x a hfull]
    exact hequiv l (B y)

theorem conjugate_full_fixedSet_model_of_abstract_isomorphism
    [Finite G] {F : Type v} [Group F] [Finite F] {Ξ : Type w} [MulAction F Ξ]
    (H : Subgroup G) (z x g : G) (a : pointRightCosetSpace H)
    (hfull : elementFixedSet H x = numeratorRightOrbit H (localInvolutionPointHull z x) a)
    (hP : fusionStronglyEmbedded
      ((rightCosetStabilizer H a).subgroupOf (localInvolutionPointHull z x)))
    (hrank : TwoRankAtLeastTwo F) (htrans : MulAction.IsPretransitive F Ξ)
    (b : Ξ) (hB : fusionStronglyEmbedded (MulAction.stabilizer F b))
    (e : localInvolutionPointHull z x ≃* F) :
    letI := hullFixedSetAction H z x
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
        (elementFixedSet H (rightConjugateElem x g)) := by
  let := hullFixedSetAction H z x
  let := hullFixedSetAction H z (rightConjugateElem x g)
  obtain ⟨E, f, _, hbase, hsource⟩ := original_full_fixedSet_model_of_abstract_isomorphism
    H z x a hfull hP hrank htrans b hB e
  refine ⟨E, f, hsource, conjugate_model_equivariant H z x g E f hsource, ?_,
    conjugate_model_transitive H z x g E f hsource htrans⟩
  intro y hy
  rw [conjugate_model_original_point]
  exact hbase y hy

end CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
