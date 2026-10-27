module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimePairs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowExtension
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem right_conjugate_point_class_card (H : Subgroup G) (z x : G) :
    Nat.card (conjugacyWithin (rightConjugate H x) (rightConjugateElem z x)) =
      Nat.card (conjugacyWithin H z) := by
  simpa only [rightConjugate, Subgroup.conjBy, rightConjugateElem,
    MulAut.conj_apply, inv_inv] using
    conjugacyWithin_card_map_automorphism H z (MulAut.conj x⁻¹)

theorem pair_specified_sylow_flip
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (p : ℕ) (hp : p.Prime)
    (Q : Sylow p (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)) :
    ∃ r ∈ involutionPointClass z,
      pointRightCosetMul H a r = b ∧ pointRightCosetMul H b r = a ∧
      r ∈ Subgroup.normalizer
        (((Q : Subgroup (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)).map
          (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G).subtype :
            Subgroup G) : Set G) ∧
      Nat.card (conjugacyWithin
        ((Q : Subgroup (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)).map
          (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G).subtype) r) =
        p ^ (Nat.card (conjugacyWithin H z)).factorization p := by
  revert hab Q
  refine Quotient.inductionOn₂ a b ?_
  intro x y hab Q
  let Hx := rightConjugate H x
  let zx := rightConjugateElem z x
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
  dsimp only [rightCosetMk] at hB
  dsimp only [rightCosetMk] at hbase hbetaImage
  revert Q
  rw [← hB]
  intro Q
  obtain ⟨T, _, hzT, hzcenterT⟩ := central_sylow_right_conjugate S hzS hzcenter x
  obtain ⟨r, hr, hrnorm, hrcard⟩ := base_pair_specified_sylow_flip
    (local_embedding_right_conjugate h x) T hzT hzcenterT hbeta p hp Q
  have hclass : involutionPointClass zx = involutionPointClass z := pointClass_eq_of_mem
    (show zx ∈ involutionPointClass z from ⟨x, rfl⟩)
  refine ⟨r, hclass ▸ hr.1, ?_, ?_, hrnorm, ?_⟩
  · rw [pointRightCosetMul_eq_translate, ← hbase, ← hbetaImage,
      ← rebaseRightCoset_translate]
    exact congrArg (rebaseRightCoset H x) hr.2
  · rw [pointRightCosetMul_eq_translate, ← hbase, ← hbetaImage,
      ← rebaseRightCoset_translate]
    exact congrArg (rebaseRightCoset H x)
      ((involution_point_uniform_pair_flips (local_embedding_right_conjugate h x)
        beta hbeta).2.1 r hr)
  · rw [right_conjugate_point_class_card] at hrcard
    exact hrcard

theorem base_pair_invariant_subgroup_flip_card_le
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (p : ℕ) (hp : p.Prime) (V : Subgroup G)
    (hVB : V ≤ pairPointStabilizer H beta) (hV : IsPGroup p V)
    (hVnorm : t ∈ Subgroup.normalizer (V : Set G)) :
    Nat.card (conjugacyWithin V t) ≤ p ^ (Nat.card (conjugacyWithin H z)).factorization p := by
  let B := pairPointStabilizer H beta
  let K := pairFlipGroup H beta t
  let BK := B.subgroupOf K
  let J := (pairOddCore H beta).subgroupOf K
  let VK := V.subgroupOf K
  let tK : K := ⟨t, flip_mem_pairFlipGroup H beta t⟩
  let : BK.Normal := pair_stabilizer_normal h.distinguished_order hbeta ht
  let : J.Normal := pairOddCore_normal_in_pair_group h.distinguished_order hbeta ht
  have hVK : V ≤ K := hVB.trans (pairPointStabilizer_le_pairFlipGroup H beta t)
  have hVtwo : IsPGroup p VK := hV.of_injective
    (Subgroup.subgroupOfEquivOfLe hVK).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hVK).injective
  have hVKimage : VK.map K.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVK
  have hVKnorm : tK ∈ Subgroup.normalizer (VK : Set K) := by
    apply (normalizer_in_subgroup_iff_ambient_image K VK tK).mpr
    rwa [hVKimage]
  obtain ⟨Q, hVQ, hQnorm⟩ := invariant_subgroup_extends p hp BK J VK tK
    (pair_flip_restriction_order_two h.distinguished_order ht)
    (pair_odd_core_restriction_odd H beta t)
    (pair_odd_core_restriction_le_stabilizer H beta t)
    (pair_flip_zStar_factorization h S hzS hzcenter hbeta ht).1
    (Subgroup.subgroupOf_mono K hVB) hVtwo hVKnorm
  obtain ⟨P, hPimage⟩ := sylow_subgroupOf_extension_ambient_image p hp B K
    (pairPointStabilizer_le_pairFlipGroup H beta t) Q
  have hVP : V ≤ (P : Subgroup B).map B.subtype := by
    rw [hPimage, ← hVKimage]
    exact Subgroup.map_mono hVQ
  have hPnorm : t ∈ Subgroup.normalizer (((P : Subgroup B).map B.subtype : Subgroup G) : Set G) := by
    rw [hPimage]
    exact (normalizer_in_subgroup_iff_ambient_image K _ tK).mp hQnorm
  exact (conjugacyWithin_card_le hVP t).trans_eq
    (pair_invariant_sylow_flip_class_card h S hzS hzcenter hbeta ht p hp P hPnorm)

theorem pair_invariant_subgroup_flip_card_le
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (t : G) (ht : t ∈ involutionPointClass z)
    (htflip : pointRightCosetMul H a t = b)
    (p : ℕ) (hp : p.Prime) (V : Subgroup G)
    (hVB : V ≤ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
    (hV : IsPGroup p V) (hVnorm : t ∈ Subgroup.normalizer (V : Set G)) :
    Nat.card (conjugacyWithin V t) ≤ p ^ (Nat.card (conjugacyWithin H z)).factorization p := by
  revert hab htflip hVB
  refine Quotient.inductionOn₂ a b ?_
  intro x y hab htflip hVB
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
  dsimp only [rightCosetMk] at hB
  have hVB' : V ≤ pairPointStabilizer Hx beta := hB ▸ hVB
  obtain ⟨T, _, hzT, hzcenterT⟩ := central_sylow_right_conjugate S hzS hzcenter x
  have htclass : t ∈ involutionPointClass (rightConjugateElem z x) :=
    (pointClass_eq_of_mem (show rightConjugateElem z x ∈ involutionPointClass z from
      ⟨x, rfl⟩)).symm ▸ ht
  have htfiber : t ∈ rightPairFlipFiber Hx (rightConjugateElem z x) beta := by
    refine ⟨htclass, ?_⟩
    apply rebaseRightCoset_injective H x
    rw [rebaseRightCoset_translate, hbase, hbetaImage]
    exact (pointRightCosetMul_eq_translate H _ t) ▸ htflip
  have hc := base_pair_invariant_subgroup_flip_card_le (local_embedding_right_conjugate h x)
    T hzT hzcenterT hbeta htfiber p hp V hVB' hV hVnorm
  rw [right_conjugate_point_class_card] at hc
  exact hc

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
