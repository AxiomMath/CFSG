module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullRelativeSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairKernel

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe v

variable {G : Type v} [Group G] [Finite G]

theorem original_central_sylow_entire_point_index_and_oddness
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (u : G) (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let M := Subgroup.centralizer ({u} : Set G)
    ((H ⊓ M).subgroupOf M).index = Nat.card (elementFixedSet H u) ∧
      Odd ((H ⊓ M).subgroupOf M).index := by
  let M := Subgroup.centralizer ({u} : Set G)
  let := originalCentralizerFixedSetAction H u
  obtain ⟨_hdoubleL, hdoubleM, _hdegree⟩ :=
    original_native_hull_and_centralizer_action_degree h S hzS hzcenter
      u huH hu huz hescape hrank
  let := hdoubleM
  let : MulAction.IsPretransitive M (elementFixedSet H u) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  let a : elementFixedSet H u := ⟨rightCosetMk H 1,
    (mem_point_right_stabilizer_iff H (rightCosetMk H 1) u).mp
      (rightCosetStabilizer_base H |>.symm ▸ huH)⟩
  have hstab : MulAction.stabilizer M a = (H ⊓ M).subgroupOf M := by
    rw [originalCentralizerFixedSetAction_stabilizer, rightCosetStabilizer_base]
    ext m
    exact ⟨fun hm => ⟨hm, m.property⟩, fun hm => hm.1⟩
  have hindex : ((H ⊓ M).subgroupOf M).index = Nat.card (elementFixedSet H u) := by
    rw [← hstab]
    exact MulAction.index_stabilizer_of_transitive M a
  obtain ⟨_hmodel, _hcore, _hB, _hfull, aexp, i, haexp, hi, _hAt,
    _helem, _hUB, _hUset, _hUcard, _hfour, _hBindex, hcard, _hident, _hdouble⟩ :=
    original_central_sylow_native_fixedSet_model h S hzS hzcenter
      u huH hu huz hescape hrank
  have haexpNe : aexp ≠ 0 := by omega
  have hiNe : i ≠ 0 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    omega
  have heven : Even ((2 ^ aexp) ^ i) :=
    (Nat.even_pow.mpr ⟨by decide, haexpNe⟩).pow_of_ne_zero hiNe
  refine ⟨hindex, ?_⟩
  rw [hindex, hcard]
  exact heven.add_one

theorem original_minimal_failure_entire_point_index_and_oddness
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (u : G) (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let M := Subgroup.centralizer ({u} : Set G)
    ((H ⊓ M).subgroupOf M).index = Nat.card (elementFixedSet H u) ∧
      Odd ((H ⊓ M).subgroupOf M).index := by
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  exact original_central_sylow_entire_point_index_and_oddness h.local_datum
    S hzS hzcenter u huH hu huz hescape hrank

theorem every_original_point_sylow_is_entire_centralizer_sylow
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (u : G) (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let M := Subgroup.centralizer ({u} : Set G)
    ∀ T1 : Sylow 2 ↥(H ⊓ M),
      ∃ T : Sylow 2 M,
        (T : Subgroup M).map M.subtype = (T1 : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype := by
  dsimp only
  intro T1
  exact every_relative_point_sylow_is_sylow _ _ inf_le_right
    (original_minimal_failure_entire_point_index_and_oddness h u huH hu huz hescape hrank).2 T1

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
