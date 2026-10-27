module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullSingleton
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullRecognition

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

@[expose] def ProperHullRankOne (H Y : Subgroup G) (z : G) (hzY : z ∈ Y) : Prop :=
  twoRank (properHull Y z) = 1 ∧
    (QuotientGroup.mk (⟨z, hzY⟩ : Y) : Y ⧸ CFSG.oddCore Y) ∈
      Subgroup.center (Y ⧸ CFSG.oddCore Y) ∧
    (Y : Set G) = (Y ⊓ Subgroup.centralizer ({z} : Set G) : Set G) *
      (properOddCore Y : Set G) ∧
    H ⊓ Y = Y ⊓ Subgroup.centralizer ({z} : Set G) ∧
    conjugacyWithin H z ∩ (Y : Set G) = {z}

@[expose] def ProperHullRankTwo (Y : Subgroup G) (z : G) : Prop :=
  2 ≤ twoRank (properHull Y z) ∧
    ⁅properOddCore Y, properHull Y z⁆ = ⊥ ∧
    R1Full (properHull Y z) ∧
    (∃ _ : (⊤ : Subgroup (properHull Y z)).Normal,
      CFSG.oddCore (properHull Y z) < ⊤ ∧ Odd (⊤ : Subgroup (properHull Y z)).index ∧
        fusionIsBenderGroup ((⊤ : Subgroup (properHull Y z)) ⧸
          (CFSG.oddCore (properHull Y z)).subgroupOf ⊤)) ∧
    fusionIsBenderGroup (properHull Y z ⧸ CFSG.oddCore (properHull Y z)) ∧
    ExplicitRankOneModel (properHull Y z ⧸ CFSG.oddCore (properHull Y z))

theorem properHull_rank_one_branch_of_triple
    {H Y : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (htriple : distinguishedTripleCentralization H z)
    (hY : Y < ⊤) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (hrank : twoRank (properHull Y z) ≤ 1) : ProperHullRankOne H Y z hzY := by
  have hpos := properHull_rank_pos (Y := Y) h.local_datum
  refine ⟨by omega, (properHull_rank_one_zStar h.local_datum hzY hrank).1,
    properHull_rank_one_ambient_factorization h.local_datum hzY hrank,
    properHull_rank_one_point_eq_centralizer_of_triple h htriple hY hzY hescape hrank,
    properHull_rank_one_global_class_singleton_of_triple h htriple hY hzY hescape hrank⟩

theorem properHull_rank_two_branch_of_triple
    {H Y : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (htriple : distinguishedTripleCentralization H z)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (hY : Y < ⊤) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (hrank : 2 ≤ twoRank (properHull Y z)) : ProperHullRankTwo Y z := by
  obtain ⟨hR1, hwhole, hmodel, hexplicit⟩ :=
    properHull_rank_two_full_recognition h hsmallerR1 hY hzY hescape hrank
  exact ⟨hrank,
    properHull_rank_two_entire_oddCore_commutator_of_triple h htriple hY hzY hescape hrank,
    hR1, hwhole, hmodel, hexplicit⟩

theorem properHull_dichotomy_of_triple
    {H Y : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (htriple : distinguishedTripleCentralization H z)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (hY : Y < ⊤) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H) :
    fusionStronglyEmbedded (H.subgroupOf (properHull Y z)) ∧
      conjugacyWithin Y z = conjugacyWithin (properHull Y z) z ∧
      Xor (ProperHullRankOne H Y z hzY) (ProperHullRankTwo Y z) := by
  refine ⟨properHull_strong_embedding h hY hzY hescape,
    properHull_class_eq h.local_datum hzY hescape, ?_⟩
  rw [xor_def]
  by_cases hrank : twoRank (properHull Y z) ≤ 1
  · refine Or.inl ⟨properHull_rank_one_branch_of_triple h htriple hY hzY hescape hrank, ?_⟩
    intro htwo
    have htwoRank := htwo.1
    omega
  · have htwoRank : 2 ≤ twoRank (properHull Y z) := by omega
    refine Or.inr ⟨properHull_rank_two_branch_of_triple
      h htriple hsmallerR1 hY hzY hescape htwoRank, ?_⟩
    intro hone
    have honeRank := hone.1
    omega

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
