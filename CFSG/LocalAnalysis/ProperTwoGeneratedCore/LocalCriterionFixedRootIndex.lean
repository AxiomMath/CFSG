module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFixedRootLifting
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFixedRootTransversal
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSubgroupSylowCounting

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

universe u

variable {G : Type u} [Group G]

theorem original_pairOddCore_normalized [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    pairPointStabilizer H beta ≤ Subgroup.normalizer (pairOddCore H beta : Set G) := by
  let : ((pairOddCore H beta).subgroupOf (pairFlipGroup H beta t)).Normal :=
    pairOddCore_normal_in_pair_group h.distinguished_order hbeta ht
  exact (pairPointStabilizer_le_pairFlipGroup H beta t).trans
    (Subgroup.le_normalizer_of_normal_subgroupOf (pairOddCore_le H beta t).2.1)

theorem original_fixed_flip_fiber_eq_centralizer_class [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hAB : A ≤ pairPointStabilizer H beta)
    (htA : t ∈ Subgroup.centralizer (A : Set G)) :
    rightPairFlipFiber H z beta ∩ (Subgroup.centralizer (A : Set G) : Set G) =
      conjugacyWithin (pairOddCore H beta ⊓ Subgroup.centralizer (A : Set G)) t := by
  rw [pair_flip_fiber_eq_odd_class h S hzS hzcenter hbeta ht]
  exact odd_conjugacyWithin_fixed_eq (pairOddCore H beta) A (pairOddCore_odd H beta) hA
    (hAB.trans (original_pairOddCore_normalized h hbeta ht)) t htA

theorem original_fixed_root_card_eq_relative_index [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hAB : A ≤ pairPointStabilizer H beta)
    (hzA : z ∈ Subgroup.centralizer (A : Set G))
    (htA : t ∈ Subgroup.centralizer (A : Set G)) :
    Nat.card {x : G // x ∈ conjugacyWithin H z ∧ x ∈ Subgroup.centralizer (A : Set G)} =
      (Subgroup.centralizer ({t} : Set G)).relIndex
        (pairOddCore H beta ⊓ Subgroup.centralizer (A : Set G)) := by
  have hcard := original_fixed_flip_card_eq_root_card h hbeta ht A hAB hzA htA
  have hfixed := original_fixed_flip_fiber_eq_centralizer_class h S hzS hzcenter hbeta ht
    A hA hAB htA
  calc
    _ = Nat.card (rightPairFlipFiber H z beta ∩
        (Subgroup.centralizer (A : Set G) : Set G) : Set G) := hcard.symm
    _ = Nat.card (conjugacyWithin
        (pairOddCore H beta ⊓ Subgroup.centralizer (A : Set G)) t) := by rw [hfixed]
    _ = _ := conjugacyWithin_card_eq_centralizer_index _ t

theorem centralizer_intersection_relative_index (J A : Subgroup G) (t : G) :
    (Subgroup.centralizer ({t} : Set G)).relIndex (J ⊓ Subgroup.centralizer (A : Set G)) =
      (((J ⊓ Subgroup.centralizer (A : Set G)) ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf
        (J ⊓ Subgroup.centralizer (A : Set G))).index := by
  exact (Subgroup.inf_relIndex_left (J ⊓ Subgroup.centralizer (A : Set G))
    (Subgroup.centralizer ({t} : Set G))).symm

theorem original_fixed_root_card_eq_centralizer_index [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hWB : W ≤ pairPointStabilizer H beta)
    (hzW : z ∈ Subgroup.centralizer (W : Set G))
    (htW : t ∈ Subgroup.centralizer (W : Set G))
    (A : Subgroup G) (hAW : A ≤ W) :
    Nat.card {x : G // x ∈ conjugacyWithin H z ∧ x ∈ Subgroup.centralizer (A : Set G)} =
      (((pairOddCore H beta ⊓ Subgroup.centralizer (A : Set G)) ⊓
          Subgroup.centralizer ({t} : Set G)).subgroupOf
        (pairOddCore H beta ⊓ Subgroup.centralizer (A : Set G))).index := by
  have hA : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 W).of_injective
    (Subgroup.inclusion hAW) (Subgroup.inclusion_injective hAW)
  have hzA : z ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => Subgroup.mem_centralizer_iff.mp hzW a (hAW ha)
  have htA : t ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => Subgroup.mem_centralizer_iff.mp htW a (hAW ha)
  rw [← centralizer_intersection_relative_index]
  exact original_fixed_root_card_eq_relative_index h S hzS hzcenter hbeta ht A hA
    (hAW.trans hWB) hzA htA

end CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot
