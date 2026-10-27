module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFullCyclicFixedMotion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPairs

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFullCyclicFixed

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem containing_cyclic_sylow_whole_fixed_set
    {H Q X : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (hQtwo : IsPGroup 2 Q) (hzQ : z ∈ Q)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    [IsCyclic X] (hXcard : Nat.card X = Nat.card (conjugacyWithin H z))
    (hinverts : ∀ x ∈ X, rightConjugateElem x t = x⁻¹)
    (hclass : conjugacyWithin (pairPointStabilizer H beta) t =
      ({t} : Set G) * (X : Set G))
    (p : ℕ) (hp : p.Prime) (hdiv : p ∣ Nat.card (conjugacyWithin H z))
    (A : Sylow p X) (P : Subgroup G) (hP : IsPGroup p P)
    (hPB : P ≤ pairPointStabilizer H beta) (hAP : cyclicSylowImage X A ≤ P) :
    pointFixedSet H P = {rightCosetMk H 1, beta} := by
  obtain ⟨hodd, hpart⟩ := prime_dividing_point_class_odd_part_gt_one h S hzS hzcenter p hp hdiv
  obtain ⟨r, hr, hrP, hmotion⟩ := containing_cyclic_sylow_full_motion h S hzS hzcenter hbeta ht
    hXcard hinverts hclass p hp A P hP hPB hAP
  have hrclass : r ∈ involutionPointClass z := hr.1
  have hcard := full_motion_fixed_card_le_two h S hzS hzcenter hQH hQnormal hQtwo hzQ
    p hp hodd hpart hP r hrclass hrP hmotion
  have ha : rightCosetMk H 1 ∈ pointFixedSet H P :=
    (mem_pointFixedSet_iff H P _).mpr (hPB.trans inf_le_left)
  have hb : beta ∈ pointFixedSet H P :=
    (mem_pointFixedSet_iff H P _).mpr (hPB.trans inf_le_right)
  exact pointFixedSet_eq_pair_of_card_le_two H P _ beta hbeta.symm ha hb hcard

theorem cyclic_sylow_le_every_centralizer_sylow
    (B X : Subgroup G) [IsCyclic X] (hXB : X ≤ B)
    (hXnormal : (X.subgroupOf B).Normal)
    (p : ℕ) (hp : p.Prime) (A : Sylow p X)
    (y : G) (hy : y ∈ B ⊓ Subgroup.centralizer (X : Set G))
    (R : Sylow p (B ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G)) :
    cyclicSylowImage X A ≤
      (R : Subgroup (B ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G)).map
        (B ⊓ Subgroup.centralizer ({y} : Set G)).subtype := by
  let AG := cyclicSylowImage X A
  let C := B ⊓ Subgroup.centralizer ({y} : Set G)
  have hAX : AG ≤ X := Subgroup.map_subtype_le _
  have hAB : AG ≤ B := hAX.trans hXB
  have hAC : AG ≤ C := by
    intro x hx
    exact ⟨hAB hx, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hy.2 x (hAX hx))⟩
  have hAnormal := cyclic_sylow_image_normal B X hXB hXnormal hp A
  have hBnorm : B ≤ Subgroup.normalizer (AG : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAB).mp hAnormal
  let : (AG.subgroupOf C).Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    ((show C ≤ B from inf_le_left).trans hBnorm)
  have hAp : IsPGroup p AG := A.isPGroup'.map X.subtype
  have hApC : IsPGroup p (AG.subgroupOf C) := hAp.comap_of_injective C.subtype Subtype.coe_injective
  have hAR : AG.subgroupOf C ≤ (R : Subgroup C) := hApC.le_sylow_of_normal R
  intro x hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hAC hx⟩, hAR hx, rfl⟩

theorem centralizer_sylow_whole_fixed_set
    {H Q X : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (hQtwo : IsPGroup 2 Q) (hzQ : z ∈ Q)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    [IsCyclic X] (hXB : X ≤ pairPointStabilizer H beta)
    (hXnormal : (X.subgroupOf (pairPointStabilizer H beta)).Normal)
    (hXcard : Nat.card X = Nat.card (conjugacyWithin H z))
    (hinverts : ∀ x ∈ X, rightConjugateElem x t = x⁻¹)
    (hclass : conjugacyWithin (pairPointStabilizer H beta) t =
      ({t} : Set G) * (X : Set G))
    (p : ℕ) (hp : p.Prime) (hdiv : p ∣ Nat.card (conjugacyWithin H z))
    (A : Sylow p X) (y : G)
    (hy : y ∈ pairPointStabilizer H beta ⊓ Subgroup.centralizer (X : Set G))
    (R : Sylow p (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G)) :
    pointFixedSet H
      ((R : Subgroup (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G)).map
        (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({y} : Set G)).subtype) =
      {rightCosetMk H 1, beta} := by
  let C := pairPointStabilizer H beta ⊓ Subgroup.centralizer ({y} : Set G)
  let RG : Subgroup G := (R : Subgroup C).map C.subtype
  have hRp : IsPGroup p RG := R.isPGroup'.map C.subtype
  have hRG : RG ≤ C := Subgroup.map_subtype_le _
  have hRB : RG ≤ pairPointStabilizer H beta := hRG.trans inf_le_left
  have hAR := cyclic_sylow_le_every_centralizer_sylow _ X hXB hXnormal p hp A y hy R
  exact containing_cyclic_sylow_whole_fixed_set h S hzS hzcenter hQH hQnormal hQtwo hzQ hbeta ht
    hXcard hinverts hclass p hp hdiv A RG hRp hRB hAR

end CFSG.ProperTwoGeneratedCore.LocalCriterionFullCyclicFixed
