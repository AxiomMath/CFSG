module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorFixedOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullRank
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullRecognition

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII

universe u

variable {G : Type u} [Group G] [Finite G]

theorem original_involution_centralizer_proper
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (u : G) (hu : orderOf u = 2) :
    Subgroup.centralizer ({u} : Set G) < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro htop
  have hucenter : u ∈ Subgroup.center G :=
    Subgroup.centralizer_eq_top_iff_subset.mp htop (Set.mem_singleton u)
  exact minimalLocalFailure_no_central_involution h u hucenter hu

theorem original_centralizer_properHull_eq
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    properHull (Subgroup.centralizer ({u} : Set G)) z = localInvolutionPointHull z u := by
  let Y := Subgroup.centralizer ({u} : Set G)
  have hzY : z ∈ Y := Subgroup.mem_centralizer_singleton_iff.mpr huz.symm
  rw [← internal_hull_map Y hzY]
  exact original_internal_centralizer_hull_map h u hu huz hescape

theorem original_centralizer_hull_normal_rank_and_embedding
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    Subgroup.centralizer ({u} : Set G) < ⊤ ∧
      ((localInvolutionPointHull z u).subgroupOf
        (Subgroup.centralizer ({u} : Set G))).Normal ∧
      1 ≤ twoRank (localInvolutionPointHull z u) ∧
      fusionStronglyEmbedded (H.subgroupOf (localInvolutionPointHull z u)) := by
  let Y := Subgroup.centralizer ({u} : Set G)
  have hzY : z ∈ Y := Subgroup.mem_centralizer_singleton_iff.mpr huz.symm
  have hL := original_centralizer_properHull_eq h.local_datum u hu huz hescape
  have hnormal := properHull_normal_in_subgroup Y hzY
  have hrank := properHull_rank_pos (Y := Y) h.local_datum
  rw [hL] at hnormal hrank
  exact ⟨original_involution_centralizer_proper h u hu, hnormal, hrank,
    h.local_datum.local_embedding u hu huz hescape⟩

theorem original_centralizer_rank_two_full_recognition
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    R1Full (localInvolutionPointHull z u) ∧
      fusionIsBenderGroup (localInvolutionPointHull z u ⧸
        CFSG.oddCore (localInvolutionPointHull z u)) ∧
      ExplicitRankOneModel (localInvolutionPointHull z u ⧸
        CFSG.oddCore (localInvolutionPointHull z u)) := by
  let Y := Subgroup.centralizer ({u} : Set G)
  have hzY : z ∈ Y := Subgroup.mem_centralizer_singleton_iff.mpr huz.symm
  have hL := original_centralizer_properHull_eq h.local_datum u hu huz hescape
  have hrankL : 2 ≤ twoRank (properHull Y z) := hL.symm ▸ hrank
  obtain ⟨hR1, _hwitness, hmodel, hexplicit⟩ :=
    properHull_rank_two_full_recognition h hsmallerR1
      (original_involution_centralizer_proper h u hu) hzY hescape hrankL
  rw [hL] at hR1 hmodel hexplicit
  exact ⟨hR1, hmodel, hexplicit⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
