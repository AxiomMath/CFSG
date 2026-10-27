module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexRegularTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorNativeRootLift
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorOddKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexIntersection
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorNativeAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe v

variable {G : Type v} [Group G] [Finite G]

theorem original_native_parameter_and_action_of_central_oddCore
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (u : G) (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u))
    (hcentral : CFSG.oddCore (localInvolutionPointHull z u) ≤
      Subgroup.center (localInvolutionPointHull z u)) :
    let L := localInvolutionPointHull z u
    let F := L ⧸ CFSG.oddCore L
    let f := QuotientGroup.mk' (CFSG.oddCore L)
    let B := (H.subgroupOf L).map f
    let A := originalPointRoot H z u
    IsSimpleBenderGroup F ∧ CFSG.oddCore L ≤ H.subgroupOf L ∧ IsBorelSubgroup B ∧
      Odd (Nat.card f.ker) ∧
      elementFixedSet H u = numeratorRightOrbit H L (rightCosetMk H 1) ∧
      ∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
        IsSimpleBenderGroupAtExponent a F ∧ IsElementaryAbelian 2 A ∧ A ≤ H ⊓ L ∧
        (A : Set G) = cosetUnitSet H z u ∧
        Nat.card (cosetUnitSet H z u) = 2 ^ a ∧
        4 ≤ Nat.card (cosetUnitSet H z u) ∧
        Nat.card (cosetFixedSet H u) = Nat.card (cosetUnitSet H z u) ^ i + 1 ∧
        B.index = Nat.card (cosetUnitSet H z u) ^ i + 1 ∧
        (∃ e : cosetFixedSet H u ≃ F ⧸ B,
          e ⟨rightCosetMk H 1, (point_right_base_fixed_iff H u).mpr huH⟩ =
            QuotientGroup.mk 1 ∧
          letI := cosetFixedSetInverseRightAction H L u
            (localInvolutionPointHull_le_centralizer z u)
          ∀ l : L, ∀ y : cosetFixedSet H u, e (l • y) = f l • e y) := by
  let L := localInvolutionPointHull z u
  let F := L ⧸ CFSG.oddCore L
  let f := QuotientGroup.mk' (CFSG.oddCore L)
  let B := (H.subgroupOf L).map f
  let A := originalPointRoot H z u
  obtain ⟨hmodel, hcore, hB⟩ := original_local_hull_native_model_and_borel
    h u hu huz hescape hrank
  have hfull := original_central_sylow_local_hull_full_fixed_set
    h S hzS hzcenter u huH hu huz hescape
  have hodd : Odd (Nat.card f.ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.ComponentClassification.OddCore.odd_card L
  have hker : f.ker ≤ H.subgroupOf L := by
    rw [QuotientGroup.ker_mk']
    exact hcore
  obtain ⟨phi, hbase, hequiv⟩ := original_full_fixedSet_image_coset_identification
    H z u hfull f (QuotientGroup.mk'_surjective (CFSG.oddCore L)) hker
  obtain ⟨a, i, ha, hi, hmodelAt, helem, hAL, hAset, hAcard, hfour, hindex,
    _hAC, _hnormal, _htrans⟩ :=
    original_native_whole_point_root_of_central_oddCore h u hu huz hescape hrank hcentral
  have hset : (A : Set G) = cosetUnitSet H z u := hAset
  have hq : Nat.card (cosetUnitSet H z u) = 2 ^ a := hset ▸ hAcard
  have hqfour : 4 ≤ Nat.card (cosetUnitSet H z u) := hset ▸ hfour
  let e : cosetFixedSet H u ≃ F ⧸ B := phi
  have hk : Nat.card (cosetFixedSet H u) = Nat.card (cosetUnitSet H z u) ^ i + 1 := by
    rw [hq]
    exact (Nat.card_congr e).trans (B.index_eq_card.symm.trans hindex)
  refine ⟨hmodel, hcore, hB, hodd, hfull, a, i, ha, hi, hmodelAt, helem, hAL,
    hset, hq, hqfour, hk, hq.symm ▸ hindex, e, hbase _ rfl, ?_⟩
  let := cosetFixedSetInverseRightAction H L u (localInvolutionPointHull_le_centralizer z u)
  intro l y
  apply hequiv l

theorem original_native_parameter_and_action_of_triple
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (htriple : distinguishedTripleCentralization H z)
    (u : G) (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let L := localInvolutionPointHull z u
    let F := L ⧸ CFSG.oddCore L
    let f := QuotientGroup.mk' (CFSG.oddCore L)
    let B := (H.subgroupOf L).map f
    let A := originalPointRoot H z u
    IsSimpleBenderGroup F ∧ CFSG.oddCore L ≤ H.subgroupOf L ∧ IsBorelSubgroup B ∧
      Odd (Nat.card f.ker) ∧
      elementFixedSet H u = numeratorRightOrbit H L (rightCosetMk H 1) ∧
      ∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
        IsSimpleBenderGroupAtExponent a F ∧ IsElementaryAbelian 2 A ∧ A ≤ H ⊓ L ∧
        (A : Set G) = cosetUnitSet H z u ∧
        Nat.card (cosetUnitSet H z u) = 2 ^ a ∧
        4 ≤ Nat.card (cosetUnitSet H z u) ∧
        Nat.card (cosetFixedSet H u) = Nat.card (cosetUnitSet H z u) ^ i + 1 ∧
        B.index = Nat.card (cosetUnitSet H z u) ^ i + 1 ∧
        (∃ e : cosetFixedSet H u ≃ F ⧸ B,
          e ⟨rightCosetMk H 1, (point_right_base_fixed_iff H u).mpr huH⟩ =
            QuotientGroup.mk 1 ∧
          letI := cosetFixedSetInverseRightAction H L u
            (localInvolutionPointHull_le_centralizer z u)
          ∀ l : L, ∀ y : cosetFixedSet H u, e (l • y) = f l • e y) := by
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hcentral := (original_centralizer_rank_two_retained_odd_cores_of_triple
    h htriple u hu huz hescape hrank).2.2.2.1
  exact original_native_parameter_and_action_of_central_oddCore
    h.local_datum S hzS hzcenter u huH hu huz hescape hrank hcentral

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
