module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u

variable {G : Type u} [Group G]

@[expose] def cosetUnitSet (H : Subgroup G) (z u : G) : Set G :=
  {1} ∪ (involutionPointClass z ∩
    (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G))

@[expose] def translatedCosetUnitSet (H : Subgroup G) (z u : G) : Set G :=
  (fun v : G => u * v) '' cosetUnitSet H z u

theorem translated_coset_inter_pair_eq_singleton [Finite G]
    {H : Subgroup G} {z u : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hu : u ∈ pairPointStabilizer H beta) :
    translatedCosetUnitSet H z u ∩ (pairPointStabilizer H beta : Set G) = {u} := by
  have hclassfix :=
    ((involution_point_unique_containment_action h.distinguished_mem h.distinguished_order).2
      h.unique_containment).2.1
  have hubeta : pointRightCosetMul H beta u = beta :=
    (mem_point_right_stabilizer_iff H beta u).mp hu.2
  ext s
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hs⟩
    rcases hv with hv | hv
    · simp only [Set.mem_singleton_iff.mp hv, mul_one, Set.mem_singleton_iff]
    · have hvbeta : pointRightCosetMul H beta v = beta := by
        have hsfix := (mem_point_right_stabilizer_iff H beta (u * v)).mp hs.2
        rw [← pointRightCosetMul_mul, hubeta] at hsfix
        exact hsfix
      have hvbase : pointRightCosetMul H (rightCosetMk H 1) v = rightCosetMk H 1 :=
        (point_right_base_fixed_iff H v).mpr hv.2
      obtain ⟨omega, _, huniq⟩ := hclassfix v hv.1.1
      exact (hbeta ((huniq beta hvbeta).trans (huniq _ hvbase).symm)).elim
  · intro hs
    rw [Set.mem_singleton_iff] at hs
    subst s
    exact ⟨⟨1, Set.mem_union_left _ (Set.mem_singleton 1), mul_one u⟩, hu⟩

theorem normalizer_inter_eq_centralizer_inter
    (Delta : Set G) (D : Subgroup G) (u : G)
    (hinter : Delta ∩ (D : Set G) = {u}) :
    Subgroup.normalizer Delta ⊓ D =
      (Subgroup.normalizer Delta ⊓ Subgroup.centralizer ({u} : Set G)) ⊓ D := by
  have humem : u ∈ Delta ∩ (D : Set G) := by rw [hinter]; exact Set.mem_singleton u
  ext x
  constructor
  · rintro ⟨hxN, hxD⟩
    have hconj : x * u * x⁻¹ ∈ Delta :=
      (show ∀ v, v ∈ Delta ↔ x * v * x⁻¹ ∈ Delta from hxN) u |>.mp humem.1
    have hconjD : x * u * x⁻¹ ∈ D :=
      D.mul_mem (D.mul_mem hxD humem.2) (D.inv_mem hxD)
    have heq : x * u * x⁻¹ = u := by
      have hm : x * u * x⁻¹ ∈ ({u} : Set G) := hinter ▸ ⟨hconj, hconjD⟩
      exact Set.mem_singleton_iff.mp hm
    have hc : x ∈ Subgroup.centralizer ({u} : Set G) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hh := congrArg (fun v : G => v * x) heq
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
    exact ⟨⟨hxN, hc⟩, hxD⟩
  · rintro ⟨⟨hxN, _⟩, hxD⟩
    exact ⟨hxN, hxD⟩

theorem translated_coset_normalizer_intersection [Finite G]
    {H : Subgroup G} {z u : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hu : u ∈ pairPointStabilizer H beta) :
    Subgroup.normalizer (translatedCosetUnitSet H z u) ⊓ pairPointStabilizer H beta =
      (Subgroup.normalizer (translatedCosetUnitSet H z u) ⊓
        Subgroup.centralizer ({u} : Set G)) ⊓ pairPointStabilizer H beta :=
  normalizer_inter_eq_centralizer_inter _ _ u
    (translated_coset_inter_pair_eq_singleton h beta hbeta hu)

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
