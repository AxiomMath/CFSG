module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorCentralizerHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullSingleton
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullTripleCentralization

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem original_rank_one_local_point_centralizer_and_class
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (w : G) (hw : orderOf w = 2) (hwz : Commute w z) (hwt : Commute w t)
    (hrank : twoRank (localInvolutionPointHull z w) ≤ 1) :
    H ⊓ Subgroup.centralizer ({w} : Set G) =
        Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ∧
      conjugacyWithin H z ∩
        (Subgroup.centralizer ({w} : Set G) : Set G) = {z} := by
  let Y := Subgroup.centralizer ({w} : Set G)
  have hzY : z ∈ Y := Subgroup.mem_centralizer_singleton_iff.mpr hwz.symm.eq
  have hescape : ¬ Y ≤ H := fun hle => pair_flip_not_mem_point hbeta ht
    (hle (Subgroup.mem_centralizer_singleton_iff.mpr hwt.symm.eq))
  have hY : Y < ⊤ := original_involution_centralizer_proper h w hw
  have hL := original_centralizer_properHull_eq h.local_datum w hw hwz hescape
  have hrankP : twoRank (properHull Y z) ≤ 1 := by
    rw [hL]
    exact hrank
  have htriple :=
    properHull_minimal_failure_distinguished_triple_centralization h hcomm hsmallerR1
  exact ⟨properHull_rank_one_point_eq_centralizer_of_triple
      h htriple hY hzY hescape hrankP,
    properHull_rank_one_global_class_singleton_of_triple
      h htriple hY hzY hescape hrankP⟩

theorem original_rank_one_entire_local_inversion_set_eq_bot
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (w : G) (hw : orderOf w = 2) (hwz : Commute w z) (hwt : Commute w t)
    (hrank : twoRank (localInvolutionPointHull z w) ≤ 1) :
    ((⊥ : Subgroup G) : Set G) = {x : G | x ∈ pairOddCore H beta ⊓
      Subgroup.centralizer ({w} : Set G) ∧ rightConjugateElem x t = x⁻¹} := by
  have hpoint := (original_rank_one_local_point_centralizer_and_class
    h hcomm hsmallerR1 beta hbeta t ht w hw hwz hwt hrank).1
  have htorder := order_two_of_mem_pointClass h.local_datum.distinguished_order ht.1
  have htt : t * t = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp htorder).1
  ext x
  constructor
  · intro hx
    have hxone : x = 1 := Subgroup.mem_bot.mp hx
    rw [hxone]
    exact ⟨(pairOddCore H beta ⊓ Subgroup.centralizer ({w} : Set G)).one_mem,
      by simp only [rightConjugateElem, inv_one, mul_one, inv_mul_cancel]⟩
  · rintro ⟨⟨hxI, hxw⟩, hxinv⟩
    apply Subgroup.mem_bot.mpr
    by_contra hne
    have hxH : x ∈ H := (pairOddCore_le H beta t).2.2 hxI
    have hxpoint : x ∈ H ⊓ Subgroup.centralizer ({w} : Set G) := ⟨hxH, hxw⟩
    rw [hpoint] at hxpoint
    have hxz : Commute x z := Subgroup.mem_centralizer_singleton_iff.mp hxpoint.2
    obtain ⟨a, ha⟩ := inverted_odd_element_mul_involution_conjugate
      (pairOddCore H beta) (pairOddCore_odd H beta) htt hxI hxinv
    have hxtclass : x * t ∈ involutionPointClass z :=
      ha ▸ pointClass_right_conjugate_mem ht.1 (a : G)
    have hprod : (x * t) * t = x := by rw [mul_assoc, htt, mul_one]
    have hprodne : (x * t) * t ≠ 1 := by rwa [hprod]
    have hprodcomm : Commute ((x * t) * t) z := by rwa [hprod]
    exact pair_flip_not_mem_point hbeta ht
      (pointClass_factors_mem_of_product_centralizing
        h.local_datum hxtclass ht.1 hprodne hprodcomm).2

theorem original_rank_one_local_fixed_root_card_eq_one
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (w : G) (hw : orderOf w = 2) (hwz : Commute w z) (hwt : Commute w t)
    (hrank : twoRank (localInvolutionPointHull z w) ≤ 1) :
    Nat.card ↥(conjugacyWithin H z ∩
      (Subgroup.centralizer ({w} : Set G) : Set G)) = 1 := by
  rw [(original_rank_one_local_point_centralizer_and_class
    h hcomm hsmallerR1 beta hbeta t ht w hw hwz hwt hrank).2]
  exact Nat.card_unique

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
