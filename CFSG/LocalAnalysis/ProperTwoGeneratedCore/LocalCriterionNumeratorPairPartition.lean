module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullExhaustion

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
open CFSG.BenderSuzuki.PFAppendixIII

universe v

variable {G : Type v} [Group G]

theorem original_centralizer_hull_subgroupOf_two_pretransitive
    (H : Subgroup G) (z u : G)
    (hdouble : letI := hullFixedSetAction H z u
      MulAction.IsMultiplyPretransitive (localInvolutionPointHull z u)
        (elementFixedSet H u) 2) :
    letI := originalCentralizerFixedSetAction H u
    MulAction.IsMultiplyPretransitive
      ((localInvolutionPointHull z u).subgroupOf (Subgroup.centralizer ({u} : Set G)))
        (elementFixedSet H u) 2 := by
  let := hullFixedSetAction H z u
  let := originalCentralizerFixedSetAction H u
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨l, hla, hlb⟩ := MulAction.is_two_pretransitive_iff.mp hdouble hab hcd
  let lM := Subgroup.inclusion (localInvolutionPointHull_le_centralizer z u) l
  refine ⟨⟨lM, l.property⟩, ?_, ?_⟩
  · exact (originalCentralizerFixedSetAction_hull_inclusion H z u l a).trans hla
  · exact (originalCentralizerFixedSetAction_hull_inclusion H z u l b).trans hlb

variable [Finite G]

theorem original_native_pair_centralizer_involution_partition
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) ≤ 1)
    (u : G) (huD : u ∈ pairPointStabilizer H beta)
    (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let M := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    u ∉ L ∧
      (∀ x : G, x ∈ M → IsInvolution x → x = u ∨ x ∈ L ∨ u * x ∈ L) ∧
      {x : G | x ∈ M ∧ IsInvolution x} =
        ({u} : Set G) ∪ {x : G | x ∈ L ∧ IsInvolution x} ∪
          ((fun x : G => u * x) '' {x : G | x ∈ L ∧ IsInvolution x}) ∧
      Disjoint ({u} : Set G) {x : G | x ∈ L ∧ IsInvolution x} ∧
      Disjoint ({u} : Set G)
        ((fun x : G => u * x) '' {x : G | x ∈ L ∧ IsInvolution x}) ∧
      Disjoint {x : G | x ∈ L ∧ IsInvolution x}
        ((fun x : G => u * x) '' {x : G | x ∈ L ∧ IsInvolution x}) := by
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let LM := L.subgroupOf M
  let := originalCentralizerFixedSetAction H u
  let : LM.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (CFSG.ProperTwoGeneratedCore.local_point_hull_normalized_by_centralizer z u)
  let a : elementFixedSet H u := ⟨rightCosetMk H 1,
    (mem_point_right_stabilizer_iff H (rightCosetMk H 1) u).mp huD.1⟩
  let b : elementFixedSet H u := ⟨beta,
    (mem_point_right_stabilizer_iff H beta u).mp huD.2⟩
  have hab : a ≠ b := fun heq => hbeta (congrArg Subtype.val heq).symm
  have huH := pairPointStabilizer_le_point H beta huD
  obtain ⟨hdouble, _hdoubleM, _hdegree⟩ :=
    original_native_hull_and_centralizer_action_degree h S hzS hzcenter
      u huH hu huz hescape hrank
  have hdoubleLM := original_centralizer_hull_subgroupOf_two_pretransitive H z u hdouble
  have hpairM := original_centralizer_fixedSet_base_pair_rank_one H u a b rfl hpairRank
  have huData := original_centralizer_involution_center_and_full_fixedness H u hu
  let uM : M := ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl u).eq⟩
  have huL := original_centralizer_involution_not_mem_hull h u hu huz hescape
  have huLM : uM ∉ LM := fun hmem => huL hmem
  let zM : M := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr huz.symm⟩
  have hzLM : zM ∈ LM := distinguished_mem_localInvolutionPointHull huz
  have hzI : IsInvolution zM := by
    have hzG : IsInvolution z :=
      ⟨(orderOf_eq_prime_iff.mp h.distinguished_order).2,
        (orderOf_eq_prime_iff.mp h.distinguished_order).1⟩
    exact ⟨fun heq => hzG.ne_one (congrArg Subtype.val heq), Subtype.ext hzG.sq_eq_one⟩
  have hza : zM • a = a := by
    apply Subtype.ext
    change pointRightCosetMul H (rightCosetMk H 1) z⁻¹ = rightCosetMk H 1
    rw [inv_eq_self_of_orderOf_eq_two h.distinguished_order]
    exact (point_right_base_fixed_iff H z).mpr h.distinguished_mem
  have hcasesM := entire_involution_two_hull_cosets LM hdoubleLM a b hab hpairM
    uM huData.1 huData.2.1 huLM (huData.2.2 a) (huData.2.2 b) zM hzLM hzI hza
  have hcases : ∀ x : G, x ∈ M → IsInvolution x → x = u ∨ x ∈ L ∨ u * x ∈ L := by
    intro x hxM hx
    let xM : M := ⟨x, hxM⟩
    have hxI : IsInvolution xM :=
      ⟨fun heq => hx.ne_one (congrArg Subtype.val heq), Subtype.ext hx.sq_eq_one⟩
    rcases hcasesM xM hxI with hxu | hxL | huxL
    · exact Or.inl (congrArg Subtype.val hxu)
    · exact Or.inr (Or.inl hxL)
    · exact Or.inr (Or.inr huxL)
  have huI : IsInvolution u :=
    ⟨(orderOf_eq_prime_iff.mp hu).2, (orderOf_eq_prime_iff.mp hu).1⟩
  have htranslate (x : G) (hxM : x ∈ M) (hx : IsInvolution x) (hxu : x ≠ u) :
      IsInvolution (u * x) := by
    let xM : M := ⟨x, hxM⟩
    have hxI : IsInvolution xM :=
      ⟨fun heq => hx.ne_one (congrArg Subtype.val heq), Subtype.ext hx.sq_eq_one⟩
    have hux := central_involution_translate_isInvolution uM xM huData.1 hxI huData.2.1
      (fun heq => hxu (congrArg Subtype.val heq))
    exact ⟨fun heq => hux.ne_one (Subtype.ext heq), congrArg Subtype.val hux.sq_eq_one⟩
  refine ⟨huL, hcases, ?_, hull_involution_three_sets_disjoint L u huL⟩
  ext x
  constructor
  · intro hx
    rcases hcases x hx.1 hx.2 with hxu | hxL | huxL
    · exact Or.inl (Or.inl hxu)
    · exact Or.inl (Or.inr ⟨hxL, hx.2⟩)
    · by_cases hxu : x = u
      · exact Or.inl (Or.inl hxu)
      · refine Or.inr ⟨u * x, ⟨huxL, htranslate x hx.1 hx.2 hxu⟩, ?_⟩
        change u * (u * x) = x
        rw [← mul_assoc, ← pow_two, huI.sq_eq_one, one_mul]
  · rintro ((hx | hx) | hx)
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨uM.property, huI⟩
    · exact ⟨localInvolutionPointHull_le_centralizer z u hx.1, hx.2⟩
    · obtain ⟨l, hl, rfl⟩ := hx
      have hlM : l ∈ M := localInvolutionPointHull_le_centralizer z u hl.1
      exact ⟨M.mul_mem uM.property hlM,
        htranslate l hlM hl.2 (fun heq => huL (heq ▸ hl.1))⟩

theorem original_minimal_failure_pair_centralizer_involution_partition
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) ≤ 1)
    (u : G) (huD : u ∈ pairPointStabilizer H beta)
    (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let M := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    u ∉ L ∧
      (∀ x : G, x ∈ M → IsInvolution x → x = u ∨ x ∈ L ∨ u * x ∈ L) ∧
      {x : G | x ∈ M ∧ IsInvolution x} =
        ({u} : Set G) ∪ {x : G | x ∈ L ∧ IsInvolution x} ∪
          ((fun x : G => u * x) '' {x : G | x ∈ L ∧ IsInvolution x}) ∧
      Disjoint ({u} : Set G) {x : G | x ∈ L ∧ IsInvolution x} ∧
      Disjoint ({u} : Set G)
        ((fun x : G => u * x) '' {x : G | x ∈ L ∧ IsInvolution x}) ∧
      Disjoint {x : G | x ∈ L ∧ IsInvolution x}
        ((fun x : G => u * x) '' {x : G | x ∈ L ∧ IsInvolution x}) := by
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  exact original_native_pair_centralizer_involution_partition h.local_datum S hzS hzcenter
    beta hbeta hpairRank u huD hu huz hescape hrank

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
