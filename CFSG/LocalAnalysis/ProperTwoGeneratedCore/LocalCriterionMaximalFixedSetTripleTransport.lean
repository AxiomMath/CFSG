module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimePairTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem class_fixed_point_central_sylow_and_class_card
    {H : Subgroup G} {z t : G} (h : InvolutionPointLocalEmbedding H z)
    (T : Sylow 2 G) (hzT : z ∈ (T : Subgroup G))
    (hzcenter : (⟨z, hzT⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G))
    (ht : t ∈ involutionPointClass z) (a : pointRightCosetSpace H)
    (hta : pointRightCosetMul H a t = a) :
    (∃ S : Sylow 2 G, ∃ htS : t ∈ (S : Subgroup G),
      (⟨t, htS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G)) ∧
      Nat.card (conjugacyWithin (rightCosetStabilizer H a) t) =
        Nat.card (conjugacyWithin H z) := by
  obtain ⟨g, rfl⟩ := ht
  obtain ⟨S, _, htS, htcenter⟩ := central_sylow_right_conjugate T hzT hzcenter g
  refine ⟨⟨S, htS, htcenter⟩, ?_⟩
  have hu := ((involution_point_unique_containment_action h.distinguished_mem
    h.distinguished_order).2 h.unique_containment).2.1
  obtain ⟨_, _, huniq⟩ := hu (rightConjugateElem z g) ⟨g, rfl⟩
  have heq : a = rightCosetMk H g := (huniq a hta).trans
    (huniq _ (point_class_conjugate_fixed_rightCoset h g)).symm
  rw [heq, rightCosetStabilizer_mk]
  exact right_conjugate_point_class_card H z g

theorem class_fixed_motion_pair_sylow_fixes_third
    {H X : Subgroup G} {z t : G} (h : InvolutionPointLocalEmbedding H z)
    (T : Sylow 2 G) (hzT : z ∈ (T : Subgroup G))
    (hzcenter : (⟨z, hzT⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G))
    (ht : t ∈ involutionPointClass z)
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (hta : pointRightCosetMul H a t = a)
    (p : ℕ) (hp : p.Prime) (hX : IsPGroup p X)
    (hXB : X ≤ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
    (htX : t ∈ Subgroup.normalizer (X : Set G))
    (hmotion : p ^ (Nat.card (conjugacyWithin H z)).factorization p ≤
      Nat.card (conjugacyWithin X t)) :
    ∃ Q : Sylow p (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G),
      (Q : Subgroup (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)).map
        (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b).subtype ≤
          rightCosetStabilizer H (pointRightCosetMul H b t) := by
  obtain ⟨⟨S, htS, htcenter⟩, hclasscard⟩ :=
    class_fixed_point_central_sylow_and_class_card h T hzT hzcenter ht a hta
  have hlocal := local_point_datum_at_class_fixed_point h ht a hta
  revert hab hta hXB hclasscard hlocal
  refine Quotient.inductionOn₂ a b ?_
  intro x y hab hta hXB hclasscard hlocal
  let Hx := rightConjugate H x
  let beta := rightCosetMk Hx (x⁻¹ * y)
  have hbase : rebaseRightCoset H x (rightCosetMk Hx 1) = rightCosetMk H x := by
    rw [rebaseRightCoset_mk, mul_one]
  have hbetaImage : rebaseRightCoset H x beta = rightCosetMk H y := by
    change rebaseRightCoset H x (rightCosetMk Hx (x⁻¹ * y)) = _
    rw [rebaseRightCoset_mk, mul_inv_cancel_left]
  have hbeta : beta ≠ rightCosetMk Hx 1 := by
    intro heq
    have hh := congrArg (rebaseRightCoset H x) heq
    rw [hbase, hbetaImage] at hh
    exact hab hh.symm
  have hB : pairPointStabilizer Hx beta =
      rightCosetStabilizer H (rightCosetMk H x) ⊓
        rightCosetStabilizer H (rightCosetMk H y) := by
    unfold pairPointStabilizer
    rw [rebaseRightCoset_stabilizer H x, rebaseRightCoset_stabilizer H x,
      hbase, hbetaImage]
  have hE : triplePointStabilizer Hx t beta ≤
      rightCosetStabilizer H (pointRightCosetMul H (rightCosetMk H y) t) := by
    calc
      triplePointStabilizer Hx t beta ≤
          rightCosetStabilizer Hx (rightCosetTranslate Hx beta t) := inf_le_right
      _ = rightCosetStabilizer H (pointRightCosetMul H (rightCosetMk H y) t) := by
        rw [rebaseRightCoset_stabilizer H x, rebaseRightCoset_translate, hbetaImage,
          ← pointRightCosetMul_eq_translate]
  change InvolutionPointLocalEmbedding
    (rightCosetStabilizer H (rightCosetMk H x)) t at hlocal
  change Nat.card (conjugacyWithin (rightCosetStabilizer H (rightCosetMk H x)) t) =
    Nat.card (conjugacyWithin H z) at hclasscard
  rw [rightCosetStabilizer_mk] at hlocal hclasscard
  change Nat.card (conjugacyWithin Hx t) = Nat.card (conjugacyWithin H z) at hclasscard
  have hmotion' : p ^ (Nat.card (conjugacyWithin Hx t)).factorization p ≤
      Nat.card (conjugacyWithin X t) := by
    rw [hclasscard]
    exact hmotion
  have hcontains := ((local_involution_point_three_point_sylow_criterion
    hlocal S htS htcenter beta hbeta).2 p hp).2.1.mpr
    ⟨X, hB.symm ▸ hXB, hX, htX, hmotion'⟩
  obtain ⟨Q, hQ⟩ := hcontains
  have hQthird := hQ.trans hE
  have result : ∃ Q : Sylow p (pairPointStabilizer Hx beta),
      (Q : Subgroup (pairPointStabilizer Hx beta)).map (pairPointStabilizer Hx beta).subtype ≤
        rightCosetStabilizer H (pointRightCosetMul H (rightCosetMk H y) t) := ⟨Q, hQthird⟩
  rw [hB] at result
  exact result

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
