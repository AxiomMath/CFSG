module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedCommutation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowGeometry

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow

variable {G : Type*} [Group G]

theorem right_conjugate_normal_eq_of_same_right_coset
    (H Q : Subgroup G) (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (x y : G) (hxy : rightCosetMk H x = rightCosetMk H y) :
    rightConjugate Q x = rightConjugate Q y := by
  have hyx : y * x⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp (Quotient.exact hxy)
  have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mp hQnormal
  ext a
  rw [mem_right_conjugate_iff, mem_right_conjugate_iff]
  have hh := Subgroup.mem_normalizer_iff.mp (hnorm hyx) (x * a * x⁻¹)
  simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left] using hh

@[expose] def pointNormalTwoHull (H Q : Subgroup G) (hQH : Q ≤ H)
    (hQnormal : (Q.subgroupOf H).Normal) : pointRightCosetSpace H → Subgroup G :=
  Quotient.lift (fun g : G => rightConjugate Q g) (fun x y hxy =>
    right_conjugate_normal_eq_of_same_right_coset H Q hQH hQnormal x y (Quotient.sound hxy))

theorem pointNormalTwoHull_mk (H Q : Subgroup G) (hQH : Q ≤ H)
    (hQnormal : (Q.subgroupOf H).Normal) (g : G) :
    pointNormalTwoHull H Q hQH hQnormal (rightCosetMk H g) = rightConjugate Q g := rfl

theorem pointNormalTwoHull_full_properties [Finite G]
    {H Q : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (hQtwo : IsPGroup 2 Q) (hzQ : z ∈ Q) (gamma : pointRightCosetSpace H) :
    pointNormalTwoHull H Q hQH hQnormal gamma ≤ rightCosetStabilizer H gamma ∧
      ((pointNormalTwoHull H Q hQH hQnormal gamma).subgroupOf
        (rightCosetStabilizer H gamma)).Normal ∧
      IsPGroup 2 (pointNormalTwoHull H Q hQH hQnormal gamma) ∧
      ∀ r ∈ involutionPointClass z,
        pointRightCosetMul H gamma r = gamma →
          r ∈ pointNormalTwoHull H Q hQH hQnormal gamma := by
  refine Quotient.inductionOn gamma ?_
  intro g
  change rightConjugate Q g ≤ rightCosetStabilizer H (rightCosetMk H g) ∧
    ((rightConjugate Q g).subgroupOf (rightCosetStabilizer H (rightCosetMk H g))).Normal ∧
    IsPGroup 2 (rightConjugate Q g) ∧ _
  refine ⟨?_, ?_, right_conjugate_is_two_group Q hQtwo g, ?_⟩
  · rw [rightCosetStabilizer_mk]
    exact Subgroup.map_mono hQH
  · rw [rightCosetStabilizer_mk]
    exact right_conjugate_normal_subgroupOf H Q hQH hQnormal g
  · intro r hr hrfixed
    exact point_class_fixed_mem_right_conjugate h hQH hQnormal hzQ g hr hrfixed

end CFSG.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed
