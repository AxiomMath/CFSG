module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullAlgebra
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCountFusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerCentralizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G]

attribute [local instance] pointRightCosetOppositeMulAction

theorem native_fixedSet_eq (H : Subgroup G) (u : G) :
    LocalCriterionInvolutionCount.fixedSet (Ω := pointRightCosetSpace H) u =
      elementFixedSet H u := rfl

theorem elementFixedSet_conjugate_iff (H : Subgroup G) (u g : G)
    (a : pointRightCosetSpace H) :
    a ∈ elementFixedSet H (rightConjugateElem u g) ↔
      pointRightCosetMul H a g⁻¹ ∈ elementFixedSet H u :=
  LocalCriterionInvolutionCount.right_conjugate_fixed_iff u g a

@[expose] def elementFixedSetConjugateEquiv (H : Subgroup G) (u g : G) :
    elementFixedSet H u ≃ elementFixedSet H (rightConjugateElem u g) where
  toFun a := ⟨pointRightCosetMul H a.val g, point_right_fixed_conjugate a.property g⟩
  invFun a := ⟨pointRightCosetMul H a.val g⁻¹,
    (elementFixedSet_conjugate_iff H u g a.val).mp a.property⟩
  left_inv a := Subtype.ext (by
    simp only [pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one])
  right_inv a := Subtype.ext (by
    simp only [pointRightCosetMul_mul, inv_mul_cancel, pointRightCosetMul_one])

theorem elementFixedSetConjugateEquiv_apply (H : Subgroup G) (u g : G)
    (a : elementFixedSet H u) :
    (elementFixedSetConjugateEquiv H u g a).val = pointRightCosetMul H a.val g := rfl

theorem elementFixedSetConjugateEquiv_symm_apply (H : Subgroup G) (u g : G)
    (a : elementFixedSet H (rightConjugateElem u g)) :
    ((elementFixedSetConjugateEquiv H u g).symm a).val =
      pointRightCosetMul H a.val g⁻¹ := rfl

theorem right_coset_conjugate_intertwines (H : Subgroup G)
    (a : pointRightCosetSpace H) (x g : G) :
    pointRightCosetMul H (pointRightCosetMul H a x) g =
      pointRightCosetMul H (pointRightCosetMul H a g) (rightConjugateElem x g) := by
  rw [pointRightCosetMul_mul, pointRightCosetMul_mul]
  congr 1
  simp only [rightConjugateElem, mul_assoc, mul_inv_cancel_left]

theorem local_hull_preserves_elementFixedSet (H : Subgroup G) (z u : G) :
    ∀ l ∈ localInvolutionPointHull z u, ∀ a ∈ elementFixedSet H u,
      pointRightCosetMul H a l ∈ elementFixedSet H u := by
  intro l hl a ha
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp
    (localInvolutionPointHull_le_centralizer z u hl)
  change pointRightCosetMul H (pointRightCosetMul H a l) u = pointRightCosetMul H a l
  rw [pointRightCosetMul_mul, hcomm, ← pointRightCosetMul_mul, ha]

@[expose, instance_reducible] def hullFixedSetAction (H : Subgroup G) (z u : G) :
    MulAction (localInvolutionPointHull z u) (elementFixedSet H u) :=
  pointInvariantSetInverseRightAction H (localInvolutionPointHull z u)
    (elementFixedSet H u) (local_hull_preserves_elementFixedSet H z u)

theorem elementFixedSetConjugateEquiv_equivariant (H : Subgroup G) (z u g : G) :
    letI := hullFixedSetAction H z u
    letI := hullFixedSetAction H z (rightConjugateElem u g)
    ∀ (l : localInvolutionPointHull z u) (a : elementFixedSet H u),
      elementFixedSetConjugateEquiv H u g (l • a) =
        localHullConjugateEquiv z u g l • elementFixedSetConjugateEquiv H u g a := by
  let := hullFixedSetAction H z u
  let := hullFixedSetAction H z (rightConjugateElem u g)
  intro l a
  apply Subtype.ext
  change pointRightCosetMul H (pointRightCosetMul H a.val l.val⁻¹) g =
    pointRightCosetMul H (pointRightCosetMul H a.val g)
      (localHullConjugateEquiv z u g l : G)⁻¹
  rw [localHullConjugateEquiv_apply]
  simpa only [rightConjugateElem, mul_inv_rev, inv_inv, mul_assoc] using
    right_coset_conjugate_intertwines H a.val l.val⁻¹ g

theorem conjugate_elementFixedSet_card (H : Subgroup G) (u g : G) :
    Nat.card (elementFixedSet H (rightConjugateElem u g)) =
      Nat.card (elementFixedSet H u) :=
  (Nat.card_congr (elementFixedSetConjugateEquiv H u g)).symm

end CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
