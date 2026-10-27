module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairGeometry

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

variable {G : Type v} [Group G] [Finite G]

theorem original_native_hull_and_centralizer_action_degree
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (u : G) (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let L := localInvolutionPointHull z u
    let M := Subgroup.centralizer ({u} : Set G)
    letI := hullFixedSetAction H z u
    letI := originalCentralizerFixedSetAction H u
    MulAction.IsMultiplyPretransitive L (elementFixedSet H u) 2 ∧
      MulAction.IsMultiplyPretransitive M (elementFixedSet H u) 2 ∧
      5 ≤ Nat.card (elementFixedSet H u) := by
  let := hullFixedSetAction H z u
  let := originalCentralizerFixedSetAction H u
  obtain ⟨_hmodel, _hcore, _hB, _hfull, a, i, ha, hi, _hAt,
    _helem, _hUB, _hUset, _hUcard, _hfour, _hindex, hcard, _hident, hdouble⟩ :=
    original_central_sylow_native_fixedSet_model h S hzS hzcenter u huH hu huz hescape hrank
  have hiPos : i ≠ 0 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    omega
  have hfour : 4 ≤ 2 ^ a := by
    calc
      4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) ha
  have hdegree : 5 ≤ Nat.card (elementFixedSet H u) := by
    have hpower := Nat.le_self_pow hiPos (2 ^ a)
    omega
  exact ⟨hdouble, original_centralizer_two_pretransitive_of_hull H z u hdouble, hdegree⟩

theorem original_native_pair_whole_kernel_and_two_fixed_points
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
    let K := (Subgroup.centralizer (L : Set G)).subgroupOf M
    letI := originalCentralizerFixedSetAction H u
    5 ≤ Nat.card (elementFixedSet H u) ∧ u ∉ L ∧
      (∀ (k : M), k ∈ K → ∀ x : elementFixedSet H u, k • x = x) ∧
      {x : G | x ∈ M ∧ x ∈ Subgroup.centralizer (L : Set G) ∧ IsInvolution x} = {u} ∧
      (∀ (x : M), IsInvolution x → ∀ a b : elementFixedSet H u,
        a ≠ b → x • a = a → x • b = b → (x : G) = u) := by
  let M := Subgroup.centralizer ({u} : Set G)
  let := originalCentralizerFixedSetAction H u
  have huH := pairPointStabilizer_le_point H beta huD
  let a : elementFixedSet H u := ⟨rightCosetMk H 1,
    (mem_point_right_stabilizer_iff H (rightCosetMk H 1) u).mp huD.1⟩
  let b : elementFixedSet H u := ⟨beta, (mem_point_right_stabilizer_iff H beta u).mp huD.2⟩
  have hab : a ≠ b := by
    intro heq
    exact hbeta (congrArg Subtype.val heq).symm
  obtain ⟨hdouble, hdoubleM, hdegree⟩ :=
    original_native_hull_and_centralizer_action_degree h S hzS hzcenter
      u huH hu huz hescape hrank
  have hpair : twoRank ↥(rightCosetStabilizer H a.val ⊓ rightCosetStabilizer H b.val) ≤ 1 :=
    hpairRank
  obtain ⟨hfix, hsingle⟩ := original_whole_hull_centralizer_fixedness_and_involution
    H z u hu hdouble (by omega) a b hpair
  have hpairM := original_centralizer_fixedSet_base_pair_rank_one H u a b rfl hpairRank
  have huData := original_centralizer_involution_center_and_full_fixedness H u hu
  let uM : M := ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl u).eq⟩
  refine ⟨hdegree, original_centralizer_involution_not_mem_hull h u hu huz hescape,
    hfix, hsingle, ?_⟩
  intro x hx c d hcd hxc hxd
  exact congrArg Subtype.val (involution_with_two_fixed_points_eq_central hdoubleM
    a b hab hpairM uM x huData.1 hx huData.2.1
    (huData.2.2 a) (huData.2.2 b) c d hcd hxc hxd)

theorem original_minimal_failure_pair_whole_kernel
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) ≤ 1)
    (u : G) (huD : u ∈ pairPointStabilizer H beta)
    (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let M := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    let K := (Subgroup.centralizer (L : Set G)).subgroupOf M
    letI := originalCentralizerFixedSetAction H u
    M < ⊤ ∧ 5 ≤ Nat.card (elementFixedSet H u) ∧ u ∉ L ∧
      (∀ (k : M), k ∈ K → ∀ x : elementFixedSet H u, k • x = x) ∧
      {x : G | x ∈ M ∧ x ∈ Subgroup.centralizer (L : Set G) ∧ IsInvolution x} = {u} ∧
      (∀ (x : M), IsInvolution x → ∀ a b : elementFixedSet H u,
        a ≠ b → x • a = a → x • b = b → (x : G) = u) := by
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  exact ⟨original_involution_centralizer_proper h u hu,
    original_native_pair_whole_kernel_and_two_fixed_points h.local_datum S hzS hzcenter
      beta hbeta hpairRank u huD hu huz hescape hrank⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
