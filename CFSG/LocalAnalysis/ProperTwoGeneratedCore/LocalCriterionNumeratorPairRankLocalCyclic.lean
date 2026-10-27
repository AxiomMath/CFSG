module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankLocalNormality
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankLocalRankOne

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem original_local_cyclic_commutator_and_normality
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (w : G) (hw : orderOf w = 2) (hwz : Commute w z) (hwt : Commute w t) :
    let C := pairOddCore H beta ⊓ Subgroup.centralizer ({w} : Set G)
    let J := rightInvolutionCommutatorSubgroup t C
    (J : Set G) = {x : G | x ∈ C ∧ rightConjugateElem x t = x⁻¹} ∧
      IsCyclic J ∧ Nat.card J = Nat.card ↥(conjugacyWithin H z ∩
        (Subgroup.centralizer ({w} : Set G) : Set G)) ∧ (J.subgroupOf C).Normal := by
  by_cases hrank : 2 ≤ twoRank (localInvolutionPointHull z w)
  · exact original_rank_two_local_cyclic_commutator_and_normality
      h hcomm hsmallerR1 S hzS hzcenter beta hbeta t ht w hw hwz hwt hrank
  · have hrankone : twoRank (localInvolutionPointHull z w) ≤ 1 := by omega
    let C := pairOddCore H beta ⊓ Subgroup.centralizer ({w} : Set G)
    have hset := original_rank_one_entire_local_inversion_set_eq_bot
      h hcomm hsmallerR1 beta hbeta t ht w hw hwz hwt hrankone
    have hodd : Odd (Nat.card C) := (pairOddCore_odd H beta).of_dvd_nat
      (Subgroup.card_dvd_of_le (show C ≤ pairOddCore H beta from inf_le_left))
    have htC : t ∈ Subgroup.normalizer (C : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨pair_flip_normalizes_ambient_odd_core h.local_datum.distinguished_order hbeta ht,
          commute_normalizes_centralizer t w hwt.symm⟩
    have htorder := order_two_of_mem_pointClass h.local_datum.distinguished_order ht.1
    obtain ⟨heq, hnormal⟩ :=
      ambient_odd_inversion_subgroup_eq_right_commutator C ⊥ hodd t htorder htC hset
    have hdelta := original_rank_one_local_fixed_root_card_eq_one
      h hcomm hsmallerR1 beta hbeta t ht w hw hwz hwt hrankone
    dsimp only
    rw [← heq]
    exact ⟨hset, isCyclic_of_subsingleton, Subgroup.card_bot.trans hdelta.symm, hnormal⟩

theorem original_local_commutator_isCyclic
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (w : G) (hw : orderOf w = 2) (hwz : Commute w z) (hwt : Commute w t) :
    IsCyclic (rightInvolutionCommutatorSubgroup t
      (pairOddCore H beta ⊓ Subgroup.centralizer ({w} : Set G))) :=
  (original_local_cyclic_commutator_and_normality
    h hcomm hsmallerR1 S hzS hzcenter beta hbeta t ht w hw hwz hwt).2.1

theorem original_local_commutator_eq_bot_of_fixed_root_card_eq_one
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (w : G) (hw : orderOf w = 2) (hwz : Commute w z) (hwt : Commute w t)
    (hdelta : Nat.card ↥(conjugacyWithin H z ∩
      (Subgroup.centralizer ({w} : Set G) : Set G)) = 1) :
    rightInvolutionCommutatorSubgroup t
      (pairOddCore H beta ⊓ Subgroup.centralizer ({w} : Set G)) = ⊥ := by
  have hcard := (original_local_cyclic_commutator_and_normality
    h hcomm hsmallerR1 S hzS hzcenter beta hbeta t ht w hw hwz hwt).2.2.1
  exact (rightInvolutionCommutatorSubgroup t
    (pairOddCore H beta ⊓ Subgroup.centralizer ({w} : Set G))).eq_bot_of_card_eq
      (hcard.trans hdelta)

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
