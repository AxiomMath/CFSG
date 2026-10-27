module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFixedRootIndex
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.PointKernelRootProductBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ShultCentralizerIndices

public section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot

universe u

variable {G : Type u} [Group G]

theorem center_eq_bot_of_simple_nonabelian (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hbot | htop
  · exact hbot
  · obtain ⟨a, b, hab⟩ := hnonab
    exact absurd (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top b) a) hab

theorem flip_not_mem_point {H : Subgroup G} {z : G} {beta : pointRightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    t ∉ H := by
  intro htH
  apply hbeta
  rw [← ht.2]
  exact (mem_rightCosetStabilizer_iff H _ t).mp (by rw [rightCosetStabilizer_base]; exact htH)

variable [Finite G]

theorem pair_hull_centralizer_inf_eq_bot {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (hgen : PairCommutatorGenerationTheorem G)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    {u : G} (huE : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (huz : Commute u z) (hut : Commute u t) :
    Subgroup.centralizer (localInvolutionPointHull z u : Set G) ⊓
      Subgroup.centralizer (localInvolutionPointHull z (u * z) : Set G) = ⊥ := by
  have huH : u ∈ H := pairPointStabilizer_le_point H beta huE
  have htH := flip_not_mem_point hbeta ht
  have htu : t ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hut.symm.eq
  have hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H := fun hle => htH (hle htu)
  obtain ⟨hsimple, hnonab⟩ := minimalLocalFailure_nonabelian_simple h
  have hhull := minimalLocalFailure_arbitrary_involution_centralizer_hull h hcomm hsmallerR1
    huH hu huz hescape
  dsimp only at hhull
  obtain ⟨-, -, -, hclassY, hclassL, -⟩ := hhull
  have htclass : t ∈ involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) :=
    ⟨ht.1, htu⟩
  rw [hclassY, hclassL] at htclass
  obtain ⟨g, hgt⟩ := htclass
  have hzt : IsConj z t := by
    obtain ⟨c, rfl⟩ := ht.1
    exact isConj_iff.mpr ⟨c⁻¹, by simp only [rightConjugateElem, inv_inv]⟩
  have hut' : u ≠ t := fun hut' => htH (hut' ▸ huH)
  have hgen' : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔
      ⁅pairOddCore H beta, Subgroup.zpowers t⁆ = ⊤ := by
    refine top_unique ?_
    rw [← hgen H z h beta hbeta t ht, pairGeneratedHull]
    refine sup_le_sup_left ?_ _
    rw [rightInvolutionCommutatorSubgroup, Subgroup.closure_le, Subgroup.commutator_comm]
    rintro _ ⟨j, rfl⟩
    have hc := Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ (Subgroup.mem_zpowers t))
      (Subgroup.inv_mem _ j.2)
    simp only [commutatorElement_def, inv_inv] at hc
    exact hc
  have htI : t ∈ Subgroup.normalizer (pairOddCore H beta : Set G) := by
    let : ((pairOddCore H beta).subgroupOf (pairFlipGroup H beta t)).Normal :=
      pairOddCore_normal_in_pair_group h.local_datum.distinguished_order hbeta ht
    exact Subgroup.le_normalizer_of_normal_subgroupOf (pairOddCore_le H beta t).2.1
      (flip_mem_pairFlipGroup H beta t)
  exact hull_centralizer_inf_eq_bot (center_eq_bot_of_simple_nonabelian hsimple hnonab)
    h.local_datum.distinguished_order hzt hu hut' huz hut (pairOddCore H beta)
    (pairOddCore_odd H beta) (original_pairOddCore_normalized h.local_datum hbeta ht huE) htI
    hgen' g.2 hgt

end CFSG.ProperTwoGeneratedCore.RankOnePair
