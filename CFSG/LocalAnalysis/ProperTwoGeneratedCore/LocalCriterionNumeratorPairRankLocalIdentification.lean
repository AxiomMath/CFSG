module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankLocalTorus

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem original_point_class_intersection_eq_conjugacyWithin
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) :
    involutionPointClass z ∩ (H : Set G) = conjugacyWithin H z := by
  rw [pointClass_inter_eq_subgroupClass h]
  ext x
  constructor
  · rintro ⟨g, hg, hgx⟩
    exact ⟨⟨g, hg⟩, hgx⟩
  · rintro ⟨g, hgx⟩
    exact ⟨g, g.property, hgx⟩

theorem original_local_inverted_element_mem_hull
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    {beta : rightCosetSpace H} {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (w : G) (hwt : Commute w t)
    (x : G) (hx : x ∈ pairOddCore H beta)
    (hxw : x ∈ Subgroup.centralizer ({w} : Set G))
    (hinv : rightConjugateElem x t = x⁻¹) :
    x ∈ localInvolutionPointHull z w := by
  have htorder : orderOf t = 2 := order_two_of_mem_pointClass h.distinguished_order ht.1
  have htt : t * t = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp htorder).1
  obtain ⟨a, ha⟩ := inverted_odd_element_mul_involution_conjugate
    (pairOddCore H beta) (pairOddCore_odd H beta) htt hx hinv
  have hxtclass : x * t ∈ involutionPointClass z :=
    ha ▸ pointClass_right_conjugate_mem ht.1 (a : G)
  have htL : t ∈ localInvolutionPointHull z w := mem_localInvolutionPointHull ht.1 hwt.symm
  have hxcomm : Commute x w := Subgroup.mem_centralizer_singleton_iff.mp hxw
  have hxtw : Commute (x * t) w := hxcomm.mul_left hwt.symm
  have hxtL : x * t ∈ localInvolutionPointHull z w :=
    mem_localInvolutionPointHull hxtclass hxtw
  have hmem := (localInvolutionPointHull z w).mul_mem hxtL
    ((localInvolutionPointHull z w).inv_mem htL)
  simpa only [mul_inv_cancel_right] using hmem

theorem original_local_torus_eq_entire_inversion_set
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (w : G) (hwt : Commute w t)
    (J : Subgroup G) (hJodd : Odd (Nat.card J))
    (hJset : (J : Set G) = {x : G | x ∈ H ⊓ rightConjugate H t ∧
      rightConjugateElem x t = x⁻¹ ∧ x ∈ localInvolutionPointHull z w}) :
    (J : Set G) = {x : G | x ∈ pairOddCore H beta ⊓
      Subgroup.centralizer ({w} : Set G) ∧ rightConjugateElem x t = x⁻¹} := by
  have htorder := order_two_of_mem_pointClass h.distinguished_order ht.1
  have htt : t * t = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp htorder).1
  have hpair : pairPointStabilizer H beta = H ⊓ rightConjugate H t := by
    have hbeta : beta = rightCosetMk H t := by
      simpa only [rightCosetTranslate_mk, one_mul] using ht.2.symm
    rw [pairPointStabilizer, hbeta, rightCosetStabilizer_base, rightCosetStabilizer_mk]
  ext x
  constructor
  · intro hx
    have hxdata := (Set.ext_iff.mp hJset x).mp hx
    obtain ⟨a, ha⟩ := inverted_odd_element_mul_involution_conjugate J hJodd htt hx hxdata.2.1
    have hxtclass : x * t ∈ involutionPointClass z :=
      ha ▸ pointClass_right_conjugate_mem ht.1 (a : G)
    have hxfix : rightCosetTranslate H (rightCosetMk H 1) x = rightCosetMk H 1 := by
      apply (mem_rightCosetStabilizer_iff H (rightCosetMk H 1) x).mp
      rw [rightCosetStabilizer_base]
      exact hxdata.1.1
    have hxtflip : x * t ∈ rightPairFlipFiber H z beta := by
      refine ⟨hxtclass, ?_⟩
      rw [← rightCosetTranslate_mul, hxfix]
      exact ht.2
    have hxI : x ∈ pairInvertedSet H beta t := by
      rw [pair_inverted_set_eq_products h S hzS hzcenter hbeta ht]
      refine ⟨x * t, hxtflip, ?_⟩
      change x * t * t = x
      rw [mul_assoc, htt, mul_one]
    exact ⟨⟨hxI.1, localInvolutionPointHull_le_centralizer z w hxdata.2.2⟩, hxI.2⟩
  · rintro ⟨⟨hxI, hxw⟩, hxinv⟩
    apply (Set.ext_iff.mp hJset x).mpr
    refine ⟨?_, hxinv, original_local_inverted_element_mem_hull h ht w hwt x hxI hxw hxinv⟩
    rw [← hpair]
    exact (pairOddCore_le H beta t).1 hxI

theorem original_rank_two_entire_local_inversion_cyclic
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (w : G) (hw : orderOf w = 2) (hwz : Commute w z) (hwt : Commute w t)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z w)) :
    ∃ a : ℕ, 2 ≤ a ∧
      IsSimpleBenderGroupAtExponent a
        (localInvolutionPointHull z w ⧸ CFSG.oddCore (localInvolutionPointHull z w)) ∧
      ∃ J : Subgroup G,
        (J : Set G) = {x : G | x ∈ pairOddCore H beta ⊓
          Subgroup.centralizer ({w} : Set G) ∧ rightConjugateElem x t = x⁻¹} ∧
        IsCyclic J ∧ Nat.card J = 2 ^ a - 1 := by
  obtain ⟨a, ha, hmodelAt, J, hJset, hJcyclic, hJcard⟩ :=
    original_rank_two_hull_cyclic_inversion_torus h hcomm hsmallerR1 beta hbeta t ht
      w hw hwz hwt hrank
  have hJodd : Odd (Nat.card J) := by
    rw [hJcard]
    exact Nat.Even.sub_odd (by have := Nat.one_le_pow a 2 (by decide); omega)
      (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  exact ⟨a, ha, hmodelAt, J,
    original_local_torus_eq_entire_inversion_set h.local_datum S hzS hzcenter
      hbeta ht w hwt J hJodd hJset, hJcyclic, hJcard⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
