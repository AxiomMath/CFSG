module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullDatum
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryRecognition

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G] [Finite G]

theorem properHull_internal_class_top {H Y : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H) :
    involutionPointHull (⟨z, distinguished_mem_properHull Y z⟩ : properHull Y z) = ⊤ := by
  let L := properHull Y z
  let zL : L := ⟨z, distinguished_mem_properHull Y z⟩
  apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
  rw [internal_hull_map L zL.property, Subgroup.map_top, Subgroup.subtype_range]
  change Subgroup.closure (conjugacyWithin L z) = L
  rw [← properHull_class_eq h hzY hescape]
  rfl

theorem properHull_internal_normalClosure_top {H Y : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H) :
    Subgroup.normalClosure
      ({(⟨z, distinguished_mem_properHull Y z⟩ : properHull Y z)} : Set (properHull Y z)) =
        ⊤ := by
  rw [← minimalLocalFailure_hull_eq_normalClosure]
  exact properHull_internal_class_top h hzY hescape

theorem properHull_normal_odd_index_eq_top {H Y : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (N : Subgroup (properHull Y z)) [N.Normal] (hodd : Odd N.index) : N = ⊤ := by
  let zL : properHull Y z := ⟨z, distinguished_mem_properHull Y z⟩
  have hzorder : orderOf zL = 2 := (Subgroup.orderOf_coe zL).symm.trans h.distinguished_order
  have hzN : zL ∈ N := square_one_mem_normal_of_odd_index N hodd
    (hzorder ▸ pow_orderOf_eq_one zL)
  apply top_unique
  rw [← properHull_internal_normalClosure_top h hzY hescape]
  exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hzN)

theorem properHull_recognition_whole_model {H Y : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (hR1 : R1Full (properHull Y z)) :
    CFSG.oddCore (properHull Y z) < ⊤ ∧
      fusionIsBenderGroup (properHull Y z ⧸ CFSG.oddCore (properHull Y z)) := by
  let L := properHull Y z
  obtain ⟨N, hNnormal, hON, hodd, hmodel⟩ := hR1.1
  let : N.Normal := hNnormal
  have hNtop := properHull_normal_odd_index_eq_top h hzY hescape N hodd
  let e : N ≃* L := (MulEquiv.subgroupCongr hNtop).trans Subgroup.topEquiv
  have hmap : ((CFSG.oddCore L).subgroupOf N).map e.toMonoidHom = CFSG.oddCore L := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact hn
    · intro hx
      exact ⟨⟨x, hON.le hx⟩, hx, rfl⟩
  let q := QuotientGroup.congr ((CFSG.oddCore L).subgroupOf N) (CFSG.oddCore L) e hmap
  exact ⟨hNtop ▸ hON, rankOneModel_of_equiv q.symm hmodel⟩

theorem properHull_recognition_whole_explicit_model {H Y : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (hR1 : R1Full (properHull Y z)) :
    ExplicitRankOneModel (properHull Y z ⧸ CFSG.oddCore (properHull Y z)) :=
  (explicitRankOneModel_iff_fusionIsBenderGroup _).mpr
    (properHull_recognition_whole_model h hzY hescape hR1).2

theorem properHull_rank_two_full_recognition {H Y : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (hY : Y < ⊤) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (hrank : 2 ≤ twoRank (properHull Y z)) :
    R1Full (properHull Y z) ∧
      (∃ _ : (⊤ : Subgroup (properHull Y z)).Normal,
        CFSG.oddCore (properHull Y z) < ⊤ ∧ Odd (⊤ : Subgroup (properHull Y z)).index ∧
          fusionIsBenderGroup ((⊤ : Subgroup (properHull Y z)) ⧸
            (CFSG.oddCore (properHull Y z)).subgroupOf ⊤)) ∧
      fusionIsBenderGroup (properHull Y z ⧸ CFSG.oddCore (properHull Y z)) ∧
      ExplicitRankOneModel (properHull Y z ⧸ CFSG.oddCore (properHull Y z)) := by
  have hR1 := hsmallerR1 (properHull Y z) (properHull_card_lt hY hzY) hrank
    ⟨H.subgroupOf (properHull Y z), properHull_strong_embedding h hY hzY hescape⟩
  have hwhole := properHull_recognition_whole_model h.local_datum hzY hescape hR1
  have hwholeWitness :
      ∃ _ : (⊤ : Subgroup (properHull Y z)).Normal,
        CFSG.oddCore (properHull Y z) < ⊤ ∧ Odd (⊤ : Subgroup (properHull Y z)).index ∧
          fusionIsBenderGroup ((⊤ : Subgroup (properHull Y z)) ⧸
            (CFSG.oddCore (properHull Y z)).subgroupOf ⊤) := by
    obtain ⟨N, hNnormal, hON, hodd, hmodel⟩ := hR1.1
    let : N.Normal := hNnormal
    have hNtop := properHull_normal_odd_index_eq_top h.local_datum hzY hescape N hodd
    subst N
    exact ⟨hNnormal, hON, hodd, hmodel⟩
  exact ⟨hR1, hwholeWitness, hwhole.2,
    properHull_recognition_whole_explicit_model h.local_datum hzY hescape hR1⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
