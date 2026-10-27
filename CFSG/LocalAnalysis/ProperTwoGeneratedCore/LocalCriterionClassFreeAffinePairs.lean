module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineInvariant
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointSylowBridge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowExtension
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem base_pair_normalized_subgroup_invariant_sylow
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (X : Subgroup G) (hXD : X ≤ pairPointStabilizer H beta)
    (hXnorm : t ∈ Subgroup.normalizer (X : Set G))
    (p : ℕ) (hp : p.Prime) :
    ∃ P : Sylow p X,
      t ∈ Subgroup.normalizer
        (((P : Subgroup X).map X.subtype : Subgroup G) : Set G) := by
  let A := pairFlipGroup H beta t
  let J := (pairOddCore H beta).subgroupOf A
  let B := X.subgroupOf A
  let tA : A := ⟨t, flip_mem_pairFlipGroup H beta t⟩
  have hXA : X ≤ A := hXD.trans (pairPointStabilizer_le_pairFlipGroup H beta t)
  let : J.Normal := pairOddCore_normal_in_pair_group h.distinguished_order hbeta ht
  have hJodd : Odd (Nat.card J) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pairOddCore_le H beta t).2.1).toEquiv]
    exact pairOddCore_odd H beta
  have hcentral : QuotientGroup.mk' J tA ∈ Subgroup.center (A ⧸ J) :=
    (pair_flip_zStar_factorization h S hzS hzcenter hbeta ht).1
  have hBnorm : tA ∈ Subgroup.normalizer (B : Set A) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    exact Subgroup.mem_normalizer_iff.mp hXnorm (x : G)
  have htorder : orderOf tA = 2 := (Subgroup.orderOf_coe tA).symm.trans
    (order_two_of_mem_pointClass h.distinguished_order ht.1)
  obtain ⟨Q, hQnorm⟩ := normalized_odd_central_quotient_invariant_sylow
    p hp J B tA htorder hJodd hBnorm hcentral
  obtain ⟨P, hPimage⟩ := sylow_subgroupOf_extension_ambient_image p hp X A hXA Q
  refine ⟨P, ?_⟩
  rw [hPimage]
  exact Subgroup.le_normalizer_map A.subtype
    (Subgroup.mem_map_of_mem A.subtype hQnorm)

theorem pair_normalized_subgroup_invariant_sylow
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (t : G) (ht : t ∈ involutionPointClass z)
    (htflip : pointRightCosetMul H a t = b)
    (X : Subgroup G)
    (hXD : X ≤ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
    (hXnorm : t ∈ Subgroup.normalizer (X : Set G))
    (p : ℕ) (hp : p.Prime) :
    ∃ P : Sylow p X,
      t ∈ Subgroup.normalizer
        (((P : Subgroup X).map X.subtype : Subgroup G) : Set G) := by
  revert hab htflip hXD
  refine Quotient.inductionOn₂ a b ?_
  intro x y hab htflip hXD
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
  have hD : pairPointStabilizer Hx beta =
      rightCosetStabilizer H (rightCosetMk H x) ⊓
        rightCosetStabilizer H (rightCosetMk H y) := by
    unfold pairPointStabilizer
    rw [rebaseRightCoset_stabilizer H x, rebaseRightCoset_stabilizer H x,
      hbase, hbetaImage]
  dsimp only [rightCosetMk] at hD
  have hXD' : X ≤ pairPointStabilizer Hx beta := hD ▸ hXD
  obtain ⟨T, _, hzT, hzcenterT⟩ := central_sylow_right_conjugate S hzS hzcenter x
  have htclass : t ∈ involutionPointClass (rightConjugateElem z x) :=
    (pointClass_eq_of_mem (show rightConjugateElem z x ∈ involutionPointClass z from
      ⟨x, rfl⟩)).symm ▸ ht
  have htfiber : t ∈ rightPairFlipFiber Hx (rightConjugateElem z x) beta := by
    refine ⟨htclass, ?_⟩
    apply rebaseRightCoset_injective H x
    rw [rebaseRightCoset_translate, hbase, hbetaImage]
    exact (pointRightCosetMul_eq_translate H _ t) ▸ htflip
  exact base_pair_normalized_subgroup_invariant_sylow (local_embedding_right_conjugate h x)
    T hzT hzcenterT beta hbeta t htfiber X hXD' hXnorm p hp

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
