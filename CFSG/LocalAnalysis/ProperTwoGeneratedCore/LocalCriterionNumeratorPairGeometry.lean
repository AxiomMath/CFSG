module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorCentralizerAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullAction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityAlgebra

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
open CFSG.TwoRankLowerBound.Helpers
open CFSG.BenderSuzuki.PFAppendixIII

universe u

variable {G : Type u} [Group G]

theorem originalCentralizerFixedSetAction_stabilizer
    (H : Subgroup G) (u : G) (a : elementFixedSet H u) :
    letI := originalCentralizerFixedSetAction H u
    MulAction.stabilizer (Subgroup.centralizer ({u} : Set G)) a =
      (rightCosetStabilizer H a.val).subgroupOf (Subgroup.centralizer ({u} : Set G)) := by
  exact TripleSylowMaximality.original_restricted_stabilizer H
    (Subgroup.centralizer ({u} : Set G)) (elementFixedSet H u)
    (original_centralizer_preserves_full_fixedSet H u) a

theorem originalCentralizerFixedSetAction_pair_stabilizer
    (H : Subgroup G) (u : G) (a b : elementFixedSet H u) :
    letI := originalCentralizerFixedSetAction H u
    MulAction.stabilizer (Subgroup.centralizer ({u} : Set G)) a ⊓
        MulAction.stabilizer (Subgroup.centralizer ({u} : Set G)) b =
      (rightCosetStabilizer H a.val ⊓ rightCosetStabilizer H b.val).subgroupOf
        (Subgroup.centralizer ({u} : Set G)) := by
  let := originalCentralizerFixedSetAction H u
  rw [originalCentralizerFixedSetAction_stabilizer,
    originalCentralizerFixedSetAction_stabilizer]
  rfl

theorem original_centralizer_involution_center_and_full_fixedness
    (H : Subgroup G) (u : G) (hu : orderOf u = 2) :
    let M := Subgroup.centralizer ({u} : Set G)
    let uM : M := ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl u).eq⟩
    letI := originalCentralizerFixedSetAction H u
    IsInvolution uM ∧ uM ∈ Subgroup.center M ∧
      ∀ a : elementFixedSet H u, uM • a = a := by
  let M := Subgroup.centralizer ({u} : Set G)
  let uM : M := ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl u).eq⟩
  let := originalCentralizerFixedSetAction H u
  have huI : IsInvolution u :=
    ⟨(orderOf_eq_prime_iff.mp hu).2, (orderOf_eq_prime_iff.mp hu).1⟩
  refine ⟨⟨fun heq => huI.ne_one (congrArg Subtype.val heq),
    Subtype.ext huI.sq_eq_one⟩, ?_, ?_⟩
  · apply Subgroup.mem_center_iff.mpr
    intro m
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp m.property
  · intro a
    apply Subtype.ext
    change pointRightCosetMul H a.val u⁻¹ = a.val
    rw [inv_eq_self_of_orderOf_eq_two hu]
    exact a.property

variable [Finite G]

theorem original_centralizer_involution_not_mem_hull
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    u ∉ localInvolutionPointHull z u :=
  fun huL => local_hull_has_no_central_involution h hu huz hescape huL

theorem original_centralizer_fixedSet_pair_rank_le_original
    (H : Subgroup G) (u : G) (a b : elementFixedSet H u) :
    letI := originalCentralizerFixedSetAction H u
    twoRank ↥(MulAction.stabilizer (Subgroup.centralizer ({u} : Set G)) a ⊓
        MulAction.stabilizer (Subgroup.centralizer ({u} : Set G)) b) ≤
      twoRank ↥(rightCosetStabilizer H a.val ⊓ rightCosetStabilizer H b.val) := by
  let M := Subgroup.centralizer ({u} : Set G)
  let D := rightCosetStabilizer H a.val ⊓ rightCosetStabilizer H b.val
  let := originalCentralizerFixedSetAction H u
  rw [originalCentralizerFixedSetAction_pair_stabilizer]
  let f : D.subgroupOf M →* D :=
    (M.subtype.comp (D.subgroupOf M).subtype).codRestrict D (fun x => x.property)
  apply le_twoRank_of_injective f
  intro x y heq
  have hval : ((x : M) : G) = ((y : M) : G) :=
    congrArg (fun d : D => (d : G)) heq
  exact Subtype.ext (Subtype.ext hval)

theorem original_centralizer_fixedSet_base_pair_rank_one
    (H : Subgroup G) (u : G) (a b : elementFixedSet H u)
    (ha : a.val = rightCosetMk H 1)
    (hrank : twoRank (pairPointStabilizer H b.val) ≤ 1) :
    letI := originalCentralizerFixedSetAction H u
    twoRank ↥(MulAction.stabilizer (Subgroup.centralizer ({u} : Set G)) a ⊓
      MulAction.stabilizer (Subgroup.centralizer ({u} : Set G)) b) ≤ 1 := by
  apply (original_centralizer_fixedSet_pair_rank_le_original H u a b).trans
  rw [ha]
  exact hrank

theorem original_whole_hull_centralizer_fixedness_and_involution
    (H : Subgroup G) (z u : G) (hu : orderOf u = 2)
    (hdouble : letI := hullFixedSetAction H z u
      MulAction.IsMultiplyPretransitive (localInvolutionPointHull z u)
        (elementFixedSet H u) 2)
    (hcard : 3 ≤ Nat.card (elementFixedSet H u))
    (a b : elementFixedSet H u)
    (hrank : twoRank ↥(rightCosetStabilizer H a.val ⊓ rightCosetStabilizer H b.val) ≤ 1) :
    let M := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    let K := (Subgroup.centralizer (L : Set G)).subgroupOf M
    letI := originalCentralizerFixedSetAction H u
    (∀ (k : M), k ∈ K → ∀ x : elementFixedSet H u, k • x = x) ∧
      {x : G | x ∈ M ∧ x ∈ Subgroup.centralizer (L : Set G) ∧ IsInvolution x} = {u} := by
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let LM := L.subgroupOf M
  let K := (Subgroup.centralizer (L : Set G)).subgroupOf M
  let := originalCentralizerFixedSetAction H u
  have hdoubleLM : MulAction.IsMultiplyPretransitive LM (elementFixedSet H u) 2 := by
    let := hullFixedSetAction H z u
    apply MulAction.is_two_pretransitive_iff.mpr
    intro c d c' d' hcd hcd'
    obtain ⟨l, hlc, hld⟩ := MulAction.is_two_pretransitive_iff.mp hdouble hcd hcd'
    let lM : M := Subgroup.inclusion (localInvolutionPointHull_le_centralizer z u) l
    refine ⟨⟨lM, l.property⟩, ?_, ?_⟩
    · exact (originalCentralizerFixedSetAction_hull_inclusion H z u l c).trans hlc
    · exact (originalCentralizerFixedSetAction_hull_inclusion H z u l d).trans hld
  have hK : K = Subgroup.centralizer (LM : Set M) := by
    ext k
    constructor
    · intro hk
      apply Subgroup.mem_centralizer_iff.mpr
      intro l _hl
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hk l.val (show l.val ∈ L from _hl)
    · intro hk
      apply Subgroup.mem_centralizer_iff.mpr
      intro l hl
      let lM : M := ⟨l, localInvolutionPointHull_le_centralizer z u hl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hk lM hl)
  have hfix : ∀ (k : M), k ∈ K → ∀ x : elementFixedSet H u, k • x = x := by
    intro k hk
    exact full_centralizer_fixes_two_pretransitive_action LM hdoubleLM hcard k (hK ▸ hk)
  have hpairRank := (original_centralizer_fixedSet_pair_rank_le_original H u a b).trans hrank
  have huData := original_centralizer_involution_center_and_full_fixedness H u hu
  let uM : M := ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl u).eq⟩
  have hsingle := full_centralizer_involutions_singleton LM hdoubleLM hcard a b hpairRank
    uM huData.1 huData.2.1 (huData.2.2 a) (huData.2.2 b)
  refine ⟨hfix, ?_⟩
  ext x
  constructor
  · rintro ⟨hxM, hxK, hx⟩
    let xM : M := ⟨x, hxM⟩
    have hxSet : xM ∈ {x : M | x ∈ Subgroup.centralizer (LM : Set M) ∧ IsInvolution x} :=
      ⟨hK ▸ hxK, ⟨fun heq => hx.ne_one (congrArg Subtype.val heq),
        Subtype.ext hx.sq_eq_one⟩⟩
    rw [hsingle] at hxSet
    exact Set.mem_singleton_iff.mpr (congrArg Subtype.val (Set.mem_singleton_iff.mp hxSet))
  · intro hx
    have hxu : x = u := Set.mem_singleton_iff.mp hx
    rw [hxu]
    refine ⟨uM.property, ?_, ?_⟩
    · apply Subgroup.mem_centralizer_iff.mpr
      intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (localInvolutionPointHull_le_centralizer z u hl)
    · exact ⟨(orderOf_eq_prime_iff.mp hu).2, (orderOf_eq_prime_iff.mp hu).1⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
