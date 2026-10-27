module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOriginalFusionAssembly
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorOddKernelFull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullOriginalSylowProduct
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineCanonicalRank

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

universe v

variable {G : Type v} [Group G] [Finite G]

theorem every_supplied_sylow_commuted_intersection_image
    {p : ℕ} [Fact p.Prime] (M H : Subgroup G) (T1 : Sylow p ↥(M ⊓ H)) :
    ∃ T1H : Sylow p ↥(H ⊓ M),
      (T1H : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype =
        (T1 : Subgroup ↥(M ⊓ H)).map (M ⊓ H).subtype := by
  let e : ↥(M ⊓ H) ≃* ↥(H ⊓ M) := MulEquiv.subgroupCongr (inf_comm M H)
  have heSurj : Function.Surjective e.toMonoidHom := by
    intro y
    obtain ⟨x, hx⟩ := e.surjective y
    exact ⟨x, hx⟩
  refine ⟨T1.mapSurjective (f := e.toMonoidHom) heSurj, ?_⟩
  change ((T1 : Subgroup ↥(M ⊓ H)).map e.toMonoidHom).map (H ⊓ M).subtype = _
  rw [Subgroup.map_map]
  have he : (H ⊓ M).subtype.comp e.toMonoidHom = (M ⊓ H).subtype := by
    ext x
    exact MulEquiv.subgroupCongr_apply (inf_comm M H) x
  rw [he]

omit [Finite G] in
theorem original_class_intersection_eq_of_entire_involution_sets
    {u : G} (hu : orderOf u = 2) (A B : Subgroup G)
    (hInv : {x : G | x ∈ A ∧ IsInvolution x} =
      {x : G | x ∈ B ∧ IsInvolution x}) :
    involutionPointClass u ∩ (A : Set G) = involutionPointClass u ∩ (B : Set G) := by
  have hI {x : G} (hx : x ∈ involutionPointClass u) : IsInvolution x := by
    have hxorder := order_two_of_mem_pointClass hu hx
    exact ⟨(orderOf_eq_prime_iff.mp hxorder).2, (orderOf_eq_prime_iff.mp hxorder).1⟩
  ext x
  constructor
  · rintro ⟨hx, hxA⟩
    exact ⟨hx, ((Set.ext_iff.mp hInv x).mp ⟨hxA, hI hx⟩).1⟩
  · rintro ⟨hx, hxB⟩
    exact ⟨hx, ((Set.ext_iff.mp hInv x).mpr ⟨hxB, hI hx⟩).1⟩

omit [Finite G] in
theorem original_order_two_partition_of_entire_involution_partition
    (A U : Subgroup G) (u : G)
    (hpartition : {x : G | x ∈ A ∧ IsInvolution x} =
      ({u} : Set G) ∪ ((U : Set G) \ {1}) ∪
        (fun w : G => u * w) '' ((U : Set G) \ {1})) :
    {x : G | x ∈ A ∧ orderOf x = 2} =
      ({u} : Set G) ∪ {w : G | w ∈ U ∧ w ≠ 1} ∪
        (fun w : G => u * w) '' {w : G | w ∈ U ∧ w ≠ 1} := by
  have horder : {x : G | x ∈ A ∧ orderOf x = 2} =
      {x : G | x ∈ A ∧ IsInvolution x} := by
    ext x
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · intro hx
      exact ⟨(orderOf_eq_prime_iff.mp hx).2, (orderOf_eq_prime_iff.mp hx).1⟩
    · intro hx
      exact orderOf_eq_prime_iff.mpr ⟨hx.2, hx.1⟩
  have hdiff : ((U : Set G) \ {1}) = {w : G | w ∈ U ∧ w ≠ 1} := by
    ext w
    exact Set.mem_sdiff_singleton
  rw [horder, hpartition, hdiff]

theorem original_prescribed_sylow_literal_full_index_of_original_rank_data
    {H : Subgroup G} {z u : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type v) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : pointRightCosetSpace H) (hb : beta ≠ rightCosetMk H 1)
    (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (huz : Commute u z) (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u))
    (hpairRank : twoRank (pairPointStabilizer H beta) ≤ 1)
    (T1 : Sylow 2 ↥(Subgroup.centralizer ({u} : Set G) ⊓ H)) :
    let M := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    let P := L ⊓ H
    let U := cosetUnitSet H z u
    let q := Nat.card U
    let Gamma := cosetFixedSet H u
    let k := Nat.card Gamma
    let D := pairPointStabilizer H beta
    let T1' := (T1 : Subgroup ↥(M ⊓ H)).map (M ⊓ H).subtype
    let T := T1' ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)))
    let Delta := involutionPointClass u ∩ (T : Set G)
    let N := Subgroup.normalizer Delta
    let F := L ⧸ CFSG.oddCore L
    let B := (H.subgroupOf L).map (QuotientGroup.mk' (CFSG.oddCore L))
    let R := properOddCore M
    R ≤ H ∧ ⁅R, L⁆ = ⊥ ∧ properOddCore L ≤ R ∧
      CFSG.oddCore L ≤ Subgroup.center L ∧ Odd (Nat.card (CFSG.oddCore L)) ∧
      u * z ∈ involutionPointClass u ∧
      L ≤ M ∧ P = L ⊓ H ∧ IsSimpleBenderGroup F ∧ IsBorelSubgroup B ∧
      CFSG.oddCore L ≤ H.subgroupOf L ∧
      ∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
        IsSimpleBenderGroupAtExponent a F ∧ q = 2 ^ a ∧ 4 ≤ q ∧ k = q ^ i + 1 ∧
        IsElementaryAbelian 2 (originalPointRoot H z u) ∧
        originalPointRoot H z u ≤ H ⊓ L ∧
        ((originalPointRoot H z u : Subgroup G) : Set G) = U ∧
        Delta = (fun w : G => u * w) '' U ∧
        Delta ∩ (D : Set G) = {u} ∧ N ≤ H ∧
        N ⊓ D = (N ⊓ Subgroup.centralizer ({u} : Set G)) ⊓ D ∧
        (∃ Q : Sylow 2 D, (Q : Subgroup D).map D.subtype ≤ N ⊓ D) ∧
        D.relIndex N = q * (k - 1) ∧
        (∀ S : Sylow 2 N, D.relIndex ((S : Subgroup N).map N.subtype) = q * (k - 1)) ∧
        q * (k - 1) ∣ Nat.card (pointRightCosetSpace H) - 1 ∧
        (Nat.card (pointRightCosetSpace H) - 1 = q * (k - 1) →
          ∀ S : Sylow 2 N, ∃ Q : Sylow 2 G,
            (Q : Subgroup G) = (S : Subgroup N).map N.subtype) := by
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let A := (T1 : Subgroup ↥(M ⊓ H)).map (M ⊓ H).subtype
  let T := A ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)))
  have hretained := original_centralizer_rank_two_retained_odd_cores
    h hcomm hsmallerR1 u hu huz hescape hrank
  have hcentral := hretained.2.2.2.1
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T1H, hT1image⟩ := every_supplied_sylow_commuted_intersection_image M H T1
  have hproduct := every_original_point_sylow_literal_intersection_entire_product
    h beta hb hpairRank u huD hu huz hescape hrank hcentral T1H
  dsimp only at hproduct
  rw [hT1image] at hproduct
  obtain ⟨S, hS⟩ := hproduct.1
  have hpartitionA : {x : G | x ∈ A ∧ IsInvolution x} =
      ({u} : Set G) ∪ ((originalPointRoot H z u : Set G) \ {1}) ∪
        (fun w : G => u * w) '' ((originalPointRoot H z u : Set G) \ {1}) :=
    hproduct.2.1.symm.trans hproduct.2.2.1
  have hpartitionS : {x : G | x ∈ (S : Subgroup M).map M.subtype ∧ orderOf x = 2} =
      ({u} : Set G) ∪ {w : G | w ∈ originalPointRoot H z u ∧ w ≠ 1} ∪
        (fun w : G => u * w) '' {w : G | w ∈ originalPointRoot H z u ∧ w ≠ 1} := by
    rw [hS]
    exact original_order_two_partition_of_entire_involution_partition
      A (originalPointRoot H z u) u hpartitionA
  have hDelta : involutionPointClass u ∩ (T : Set G) =
      involutionPointClass u ∩ (((S : Subgroup M).map M.subtype : Subgroup G) : Set G) := by
    rw [hS]
    exact original_class_intersection_eq_of_entire_involution_sets hu T A hproduct.2.1
  have hfour := LocalCriterionClassFreeAffine.not_twoRankAtLeastTwo_of_twoRank_le_one hpairRank
  have hfull := original_native_full_index_of_central_oddCore_and_complete_sylow_partition
    h hcomm beta hb huD hu huz hescape hrank hfour hcentral S hpartitionS
  dsimp only
  refine ⟨hretained.1, hretained.2.1, hretained.2.2.1, hcentral,
    hretained.2.2.2.2.1, ?_⟩
  rw [hDelta]
  exact hfull

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
