module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFullCyclicFixedAlgebra
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimePairs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeClass
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedCommutation

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFullCyclicFixed

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem cyclic_sylow_image_full_odd_part
    {H X : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hXcard : Nat.card X = Nat.card (conjugacyWithin H z))
    (p : ℕ) (hp : p.Prime) (A : Sylow p X) :
    IsPGroup p (cyclicSylowImage X A) ∧ Odd (Nat.card (cyclicSylowImage X A)) ∧
      Nat.card (cyclicSylowImage X A) =
        p ^ (Nat.card (conjugacyWithin H z)).factorization p := by
  have hAX : cyclicSylowImage X A ≤ X := Subgroup.map_subtype_le _
  refine ⟨A.isPGroup'.map X.subtype, ?_, ?_⟩
  · have hXodd : Odd (Nat.card X) := hXcard ▸ point_subgroup_full_class_card_odd h S hzS hzcenter
    exact hXodd.of_dvd_nat (Subgroup.card_dvd_of_le hAX)
  · rw [cyclic_sylow_image_card X hp A, hXcard]

theorem containing_cyclic_sylow_full_motion
    {H X : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    [IsCyclic X]
    (hXcard : Nat.card X = Nat.card (conjugacyWithin H z))
    (hinverts : ∀ x ∈ X, rightConjugateElem x t = x⁻¹)
    (hclass : conjugacyWithin (pairPointStabilizer H beta) t =
      ({t} : Set G) * (X : Set G))
    (p : ℕ) (hp : p.Prime) (A : Sylow p X)
    (P : Subgroup G) (hP : IsPGroup p P)
    (hPB : P ≤ pairPointStabilizer H beta) (hAP : cyclicSylowImage X A ≤ P) :
    ∃ r ∈ rightPairFlipFiber H z beta,
      r ∈ Subgroup.normalizer (P : Set G) ∧
      Nat.card (conjugacyWithin P r) =
        p ^ (Nat.card (conjugacyWithin H z)).factorization p := by
  let B := pairPointStabilizer H beta
  have hPinB : IsPGroup p (P.subgroupOf B) := hP.comap_of_injective B.subtype Subtype.coe_injective
  obtain ⟨R, hPR⟩ := hPinB.exists_le_sylow
  let RG : Subgroup G := (R : Subgroup B).map B.subtype
  have hPRG : P ≤ RG := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hPB hx⟩, hPR hx, rfl⟩
  obtain ⟨r, hr, hrR, hRmotion⟩ := base_pair_specified_sylow_flip h S hzS hzcenter hbeta p hp R
  have hrclass : r ∈ conjugacyWithin B t := by
    rw [← pair_flip_fiber_eq_stabilizer_class h S hzS hzcenter hbeta ht]
    exact hr
  have hrcoset : r ∈ ({t} : Set G) * (X : Set G) := hclass ▸ hrclass
  have hrinverts := cyclic_coset_inverts X t hinverts hrcoset
  have hAX : cyclicSylowImage X A ≤ X := Subgroup.map_subtype_le _
  have hrA : r ∈ Subgroup.normalizer (cyclicSylowImage X A : Set G) :=
    inversion_mem_normalizer _ r (fun x hx => hrinverts x (hAX hx))
  obtain ⟨_, hAodd, hAcard⟩ := cyclic_sylow_image_full_odd_part h S hzS hzcenter hXcard p hp A
  have hAmotion : Nat.card (conjugacyWithin (cyclicSylowImage X A) r) =
      p ^ (Nat.card (conjugacyWithin H z)).factorization p := by
    rw [odd_inversion_conjugacy_card _ r hAodd (fun x hx => hrinverts x (hAX hx)), hAcard]
  have hequal : Nat.card (conjugacyWithin (cyclicSylowImage X A) r) =
      Nat.card (conjugacyWithin RG r) := hAmotion.trans hRmotion.symm
  have hrP : r ∈ Subgroup.normalizer (P : Set G) :=
    equal_orbit_card_normalizes_intermediate _ P RG hAP hPRG r hrR hrA hequal
  refine ⟨r, hr, hrP, ?_⟩
  apply le_antisymm
  · exact (conjugacyWithin_card_le hPRG r).trans hRmotion.le
  · exact hAmotion.ge.trans (conjugacyWithin_card_le hAP r)

end CFSG.ProperTwoGeneratedCore.LocalCriterionFullCyclicFixed
