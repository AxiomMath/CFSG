module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexAssembly
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexNativeParameter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOriginalFusion
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssembly

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

universe v

variable {G : Type v} [Group G] [Finite G]

theorem original_native_full_index_of_central_oddCore_and_sylow_geometry
    {H : Subgroup G} {z u : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (beta : pointRightCosetSpace H) (hb : beta ≠ rightCosetMk H 1)
    (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (huz : Commute u z) (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u))
    (hfour : ¬ TwoRankAtLeastTwo (pairPointStabilizer H beta))
    (hcentral : CFSG.oddCore (localInvolutionPointHull z u) ≤
      Subgroup.center (localInvolutionPointHull z u))
    (T1 : Sylow 2 (Subgroup.centralizer ({u} : Set G)))
    (hpartition : ∀ x : G,
      x ∈ (T1 : Subgroup (Subgroup.centralizer ({u} : Set G))).map
        (Subgroup.centralizer ({u} : Set G)).subtype → IsInvolution x →
      x ∈ originalPointRoot H z u ∨ x ∈ translatedCosetUnitSet H z u)
    (hDelta : involutionPointClass u ∩
      (((T1 : Subgroup (Subgroup.centralizer ({u} : Set G))).map
        (Subgroup.centralizer ({u} : Set G)).subtype : Subgroup G) : Set G) =
      translatedCosetUnitSet H z u) :
    let M := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    let P := L ⊓ H
    let U := cosetUnitSet H z u
    let q := Nat.card U
    let Gamma := cosetFixedSet H u
    let k := Nat.card Gamma
    let D := pairPointStabilizer H beta
    let Delta := involutionPointClass u ∩
      (((T1 : Subgroup M).map M.subtype : Subgroup G) : Set G)
    let N := Subgroup.normalizer Delta
    let F := L ⧸ CFSG.oddCore L
    let B := (H.subgroupOf L).map (QuotientGroup.mk' (CFSG.oddCore L))
    L ≤ M ∧ P = L ⊓ H ∧ IsSimpleBenderGroup F ∧ IsBorelSubgroup B ∧
      CFSG.oddCore L ≤ H.subgroupOf L ∧
      ∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
        IsSimpleBenderGroupAtExponent a F ∧ q = 2 ^ a ∧ 4 ≤ q ∧ k = q ^ i + 1 ∧
        IsElementaryAbelian 2 (originalPointRoot H z u) ∧
        originalPointRoot H z u ≤ H ⊓ L ∧
        ((originalPointRoot H z u : Subgroup G) : Set G) = U ∧
        Delta = (fun v : G => u * v) '' U ∧
        Delta ∩ (D : Set G) = {u} ∧ N ≤ H ∧
        N ⊓ D = (N ⊓ Subgroup.centralizer ({u} : Set G)) ⊓ D ∧
        (∃ Q : Sylow 2 D, (Q : Subgroup D).map D.subtype ≤ N ⊓ D) ∧
        D.relIndex N = q * (k - 1) ∧
        (∀ S : Sylow 2 N, D.relIndex ((S : Subgroup N).map N.subtype) = q * (k - 1)) ∧
        q * (k - 1) ∣ Nat.card (pointRightCosetSpace H) - 1 ∧
        (Nat.card (pointRightCosetSpace H) - 1 = q * (k - 1) →
          ∀ S : Sylow 2 N, ∃ R : Sylow 2 G,
            (R : Subgroup G) = (S : Subgroup N).map N.subtype) := by
  let L := localInvolutionPointHull z u
  let F := L ⧸ CFSG.oddCore L
  let f := QuotientGroup.mk' (CFSG.oddCore L)
  let B := (H.subgroupOf L).map f
  have huH := pairPointStabilizer_le_point H beta huD
  obtain ⟨S0, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨hmodel, hcore, hB, hodd, _hfull, a, i, ha, hi, hAt, helem,
      hUle, hUset, hq, hqfour, hk, _hBindex, e, hbase, he⟩ :=
    original_native_parameter_and_action_of_central_oddCore
      h.local_datum S0 hzS hzcenter u huH hu huz hescape hrank hcentral
  have hconj := original_coset_full_conjugation_of_supplied_sylow_geometry
    h beta hb huD hu huz hescape (originalPointRoot H z u) hUset T1 hpartition hDelta
  have hdoubly := (minimalLocalFailureSylowFixedPointsFromProperCommutingImages h hcomm).2.2.1
  have huI : IsInvolution u :=
    ⟨(orderOf_eq_prime_iff.mp hu).2, (orderOf_eq_prime_iff.mp hu).1⟩
  have hindex := translated_coset_full_index_and_sylow_consequences
    h.local_datum beta hb huD huI huz.symm hfour hdoubly L
    (localInvolutionPointHull_le_centralizer z u) f
    (QuotientGroup.mk'_surjective (CFSG.oddCore L)) hodd B hB hmodel
    e hbase he hconj ⟨a, hq⟩ ⟨i, hk⟩
  dsimp only
  rw [hDelta]
  refine ⟨localInvolutionPointHull_le_centralizer z u, rfl, hmodel, hB, hcore,
    a, i, ha, hi, hAt, hq, hqfour, hk, helem, hUle, hUset, rfl, ?_⟩
  exact hindex

theorem original_native_full_index_of_triple_and_sylow_geometry
    {H : Subgroup G} {z u : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (htriple : distinguishedTripleCentralization H z)
    (beta : pointRightCosetSpace H) (hb : beta ≠ rightCosetMk H 1)
    (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (huz : Commute u z) (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u))
    (hfour : ¬ TwoRankAtLeastTwo (pairPointStabilizer H beta))
    (T1 : Sylow 2 (Subgroup.centralizer ({u} : Set G)))
    (hpartition : ∀ x : G,
      x ∈ (T1 : Subgroup (Subgroup.centralizer ({u} : Set G))).map
        (Subgroup.centralizer ({u} : Set G)).subtype → IsInvolution x →
      x ∈ originalPointRoot H z u ∨ x ∈ translatedCosetUnitSet H z u)
    (hDelta : involutionPointClass u ∩
      (((T1 : Subgroup (Subgroup.centralizer ({u} : Set G))).map
        (Subgroup.centralizer ({u} : Set G)).subtype : Subgroup G) : Set G) =
      translatedCosetUnitSet H z u) :
    let D := pairPointStabilizer H beta
    let Delta := involutionPointClass u ∩
      (((T1 : Subgroup (Subgroup.centralizer ({u} : Set G))).map
        (Subgroup.centralizer ({u} : Set G)).subtype : Subgroup G) : Set G)
    let N := Subgroup.normalizer Delta
    let q := Nat.card (cosetUnitSet H z u)
    let k := Nat.card (cosetFixedSet H u)
    (∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧ q = 2 ^ a ∧ 4 ≤ q ∧ k = q ^ i + 1) ∧
      Delta = translatedCosetUnitSet H z u ∧ Delta ∩ (D : Set G) = {u} ∧ N ≤ H ∧
      N ⊓ D = (N ⊓ Subgroup.centralizer ({u} : Set G)) ⊓ D ∧
      (∃ Q : Sylow 2 D, (Q : Subgroup D).map D.subtype ≤ N ⊓ D) ∧
      D.relIndex N = q * (k - 1) ∧
      (∀ S : Sylow 2 N, D.relIndex ((S : Subgroup N).map N.subtype) = q * (k - 1)) ∧
      q * (k - 1) ∣ Nat.card (pointRightCosetSpace H) - 1 ∧
      (Nat.card (pointRightCosetSpace H) - 1 = q * (k - 1) →
        ∀ S : Sylow 2 N, ∃ R : Sylow 2 G,
          (R : Subgroup G) = (S : Subgroup N).map N.subtype) := by
  have hcentral := (original_centralizer_rank_two_retained_odd_cores_of_triple
    h htriple u hu huz hescape hrank).2.2.2.1
  obtain ⟨_hLM, _hP, _hmodel, _hB, _hcore, a, i, ha, hi, _hAt, hq, hqfour, hk,
    _helem, _hUle, _hUset, hDeltaliteral, hsingle, hNH, hinter, hQ, hindex, hSylow,
    hdiv, hglobal⟩ := original_native_full_index_of_central_oddCore_and_sylow_geometry
      h hcomm beta hb huD hu huz hescape hrank hfour hcentral T1 hpartition hDelta
  exact ⟨⟨a, i, ha, hi, hq, hqfour, hk⟩, hDeltaliteral, hsingle, hNH,
    hinter, hQ, hindex, hSylow, hdiv, hglobal⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
