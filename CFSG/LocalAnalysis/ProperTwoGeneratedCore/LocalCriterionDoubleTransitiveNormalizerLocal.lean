module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerFixedCosets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer

open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

variable {G : Type*} [Group G] [Finite G]

theorem original_triple_sylow_normalizer_local_datum
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (P : Sylow p (triplePointStabilizer H z beta))
    (hzP : z ∈ Subgroup.normalizer
      (((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G)) :
    let N := Subgroup.normalizer
      (((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G)
    InvolutionPointLocalEmbedding (H.subgroupOf N) (⟨z, hzP⟩ : N) ∧
      ∃ (T : Sylow 2 N) (hzT : (⟨z, hzP⟩ : N) ∈ (T : Subgroup N)),
        (⟨(⟨z, hzP⟩ : N), hzT⟩ : (T : Subgroup N)) ∈ Subgroup.center (T : Subgroup N) := by
  have hescape := triple_sylow_normalizer_not_le_original_point h S hzS hzcenter hbeta p hp P
  obtain ⟨hlocal, hcentral⟩ := involution_point_subgroup_inheritance h _ hzP hescape
  exact ⟨hlocal, hcentral ⟨S, hzS, hzcenter⟩⟩

theorem original_triple_sylow_normalizer_base_class_flip
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (P : Sylow p (triplePointStabilizer H z beta))
    (hzP : z ∈ Subgroup.normalizer
      (((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G))
    (b : pointRightCosetSpace H)
    (hb : b ∈ pointFixedSet H ((P : Subgroup (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype)) (hbne : b ≠ rightCosetMk H 1) :
    let N := Subgroup.normalizer
      (((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G)
    ∃ s : N, ∃ n : N, rightConjugateElem (⟨z, hzP⟩ : N) n = s ∧
      pointRightCosetMul H (rightCosetMk H 1) (s : G) = b ∧
      pointRightCosetMul H b (s : G) = rightCosetMk H 1 := by
  let U : Subgroup G := (P : Subgroup (triplePointStabilizer H z beta)).map
    (triplePointStabilizer H z beta).subtype
  let N := Subgroup.normalizer (U : Set G)
  have hUH : U ≤ H := (Subgroup.map_subtype_le _).trans
    ((show triplePointStabilizer H z beta ≤ pairPointStabilizer H beta from inf_le_left).trans
      (pairPointStabilizer_le_point H beta))
  have htrans := original_triple_sylow_normalizer_transitive h S hzS hzcenter hdoubly beta hbeta p hp P hzP
  have hsurj := normalizerRightCosetFixedEmbedding_surjective H U hUH htrans
  obtain ⟨bN, hbN⟩ := hsurj (⟨b, hb⟩ : pointFixedSet H U)
  have himage : restrictedRightCosetEmbedding H N bN = b := congrArg Subtype.val hbN
  have hbNne : bN ≠ rightCosetMk (H.subgroupOf N) 1 := by
    intro heq
    apply hbne
    rw [heq, restrictedRightCosetEmbedding_mk, Subgroup.coe_one] at himage
    exact himage.symm
  obtain ⟨hlocal, _⟩ := original_triple_sylow_normalizer_local_datum h S hzS hzcenter beta hbeta p hp P hzP
  obtain ⟨s, hs⟩ := original_pair_flip_exists hlocal bN hbNne
  have hsback := (involution_point_uniform_pair_flips hlocal bN hbNne).2.1 s hs
  obtain ⟨n, hns⟩ := hs.1
  refine ⟨s, n, hns, ?_, ?_⟩
  · have hh := congrArg (restrictedRightCosetEmbedding H N) hs.2
    rw [← pointRightCosetMul_eq_translate, restrictedRightCosetEmbedding_equivariant,
      restrictedRightCosetEmbedding_mk, Subgroup.coe_one, himage] at hh
    exact hh
  · have hh := congrArg (restrictedRightCosetEmbedding H N) hsback
    rw [← pointRightCosetMul_eq_translate, restrictedRightCosetEmbedding_equivariant,
      himage, restrictedRightCosetEmbedding_mk, Subgroup.coe_one] at hh
    exact hh

end CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
