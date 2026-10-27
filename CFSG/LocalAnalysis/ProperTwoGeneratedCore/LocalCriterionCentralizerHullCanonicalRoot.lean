module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullCanonicalKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorUnifiedParameter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullOriginalSylowOrbits

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
open CFSG.BenderSuzuki.PFAppendixIII

universe v

variable {G : Type v} [Group G] [Finite G]

@[expose] def rankTwoCentralizerRootData (H : Subgroup G) (z u : G) : Prop :=
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let R := CFSG.oddCore L
  let J := L ⧸ R
  let f := QuotientGroup.mk' R
  let B := (H.subgroupOf L).map f
  let U := originalPointRoot H z u
  let _ := hullFixedSetAction H z u
  let _ := originalCentralizerFixedSetAction H u
  IsElementaryAbelian 2 U ∧ U ≤ L ∧ U ≤ H ⊓ M ∧
    (U.subgroupOf (H ⊓ M)).Normal ∧
    (U : Set G) = {1} ∪
      (involutionPointClass z ∩ (M : Set G) ∩ (H : Set G)) ∧
    (U : Set G) = {1} ∪ {x : G | x ∈ L ∧ x ∈ H ⊓ M ∧ orderOf x = 2} ∧
    4 ≤ Nat.card U ∧
    ((H ⊓ M).subgroupOf M).index = Nat.card (elementFixedSet H u) ∧
    Odd ((H ⊓ M).subgroupOf M).index ∧
    CFSG.BenderSuzuki.IsStronglyEmbedded ((L ⊓ (H ⊓ M)).subgroupOf L) ∧
    IsSimpleBenderGroup J ∧ IsBorelSubgroup B ∧ R ≤ H.subgroupOf L ∧
    elementFixedSet H u = numeratorRightOrbit H L (rightCosetMk H 1) ∧
    MulAction.IsMultiplyPretransitive L (elementFixedSet H u) 2 ∧
    MulAction.IsMultiplyPretransitive M (elementFixedSet H u) 2 ∧
    ∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
      Nat.card U = 2 ^ a ∧ IsSimpleBenderGroupAtExponent a J ∧
      B.index = (Nat.card U) ^ i + 1 ∧
      Nat.card (elementFixedSet H u) = (Nat.card U) ^ i + 1 ∧
      (∃ phi : elementFixedSet H u ≃ (J ⧸ B),
        (∀ y : elementFixedSet H u, y.val = rightCosetMk H 1 →
          phi y = QuotientGroup.mk 1) ∧
        ∀ (l : L) (y : elementFixedSet H u), phi (l • y) = f l • phi y) ∧
      ((i = 1 ∧ Nonempty (J ≃* PSL2BinaryMatrixGroup a)) ∨
        (i = 2 ∧ ∃ m : ℕ, a = 2 * m + 1 ∧ Nonempty (J ≃* SuzukiMatrixGroup m)) ∨
        (i = 3 ∧ ∃ (E : Type) (_ : Field E) (_ : Finite E) (A : HermitianForm 3 E),
          A.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
          Nat.card E = (2 ^ a) ^ 2 ∧
          Nat.card {x : E // A.conj x = x} = 2 ^ a ∧
          Nonempty (J ≃* ProjectiveSpecialUnitaryMatrixGroup A)))

theorem original_rank_two_centralizer_root_data
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type v) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (u : G) (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    rankTwoCentralizerRootData H z u := by
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let U := originalPointRoot H z u
  let _ := hullFixedSetAction H z u
  let _ := originalCentralizerFixedSetAction H u
  have hcentral := original_local_hull_entire_oddCore_central
    h hcomm hsmallerR1 u hu huz hescape hrank
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨hmodel, hB, hcore, hfull, a, i, ha, hi, hAt, helem, hUL, hUset,
    hcard, hfour, hBindex, hfixcard, hUM, hnormal, _htrans, hphi,
    hdoubleL, hdoubleM, hfamily⟩ :=
    original_native_root_degree_and_full_action_of_central_oddCore
      h.local_datum S hzS hzcenter u huH hu huz hescape hrank hcentral
  have hrootInv := original_whole_root_as_entire_hull_point_involutions
    h.local_datum u hu huz hescape U hUset
  have hindex := original_minimal_failure_entire_point_index_and_oddness
    h u huH hu huz hescape hrank
  unfold rankTwoCentralizerRootData
  simp only [order_two_iff_isInvolution]
  exact ⟨helem, hUL.trans inf_le_right, hUM, hnormal, hUset, hrootInv,
    hfour, hindex.1, hindex.2,
    original_hull_point_isStronglyEmbedded h.local_datum u hu huz hescape,
    hmodel, hB, hcore, hfull, hdoubleL, hdoubleM,
    a, i, ha, hi, hcard, hAt, hBindex, hfixcard, hphi, hfamily⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
