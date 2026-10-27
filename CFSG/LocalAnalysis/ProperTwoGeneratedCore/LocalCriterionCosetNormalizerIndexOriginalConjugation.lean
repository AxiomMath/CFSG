module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOriginalPrescribedSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexUnitAffineStabilizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexCosetTransitivity

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

universe v

variable {G : Type v} [Group G]

theorem unitCoordinateAction_isTwoPretransitive (U : Subgroup G) (u : G)
    (htrans : ∀ s : G, s ∈ (fun x : G => u * x) '' (U : Set G) →
      ∀ t : G, t ∈ (fun x : G => u * x) '' (U : Set G) →
      ∃ n : Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G)),
        rightConjugateElem s (n : G) = t)
    (hstab : ∀ s : G, s ∈ (fun x : G => u * x) '' (U : Set G) → s ≠ u →
      ∀ t : G, t ∈ (fun x : G => u * x) '' (U : Set G) → t ≠ u →
      ∃ a : (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G)) ⊓
          Subgroup.centralizer ({u} : Set G) : Subgroup G),
        rightConjugateElem s (a : G) = t) :
    letI := unitCoordinateAction U u
    MulAction.IsMultiplyPretransitive
      (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) U 2 := by
  let Delta : Set G := (fun x : G => u * x) '' (U : Set G)
  let := cosetNormalizerAction Delta
  let := unitCoordinateAction U u
  have h := cosetNormalizerAction_isTwoPretransitive Delta u
    ⟨1, U.one_mem, mul_one u⟩ htrans hstab
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  let e := unitTranslateEquiv U u
  have hab' : e a ≠ e b := fun heq => hab (e.injective heq)
  have hcd' : e c ≠ e d := fun heq => hcd (e.injective heq)
  obtain ⟨n, hn, hn'⟩ := MulAction.is_two_pretransitive_iff.mp h hab' hcd'
  refine ⟨n, e.injective ?_, e.injective ?_⟩
  · exact (unitTranslateEquiv_unitCoordinatePerm U u n a).trans hn
  · exact (unitTranslateEquiv_unitCoordinatePerm U u n b).trans hn'

theorem unitAffineHom_range_isTwoPretransitive (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x)
    (htrans : ∀ s : G, s ∈ (fun x : G => u * x) '' (U : Set G) →
      ∀ t : G, t ∈ (fun x : G => u * x) '' (U : Set G) →
      ∃ n : Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G)),
        rightConjugateElem s (n : G) = t)
    (hstab : ∀ s : G, s ∈ (fun x : G => u * x) '' (U : Set G) → s ≠ u →
      ∀ t : G, t ∈ (fun x : G => u * x) '' (U : Set G) → t ≠ u →
      ∃ a : (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G)) ⊓
          Subgroup.centralizer ({u} : Set G) : Subgroup G),
        rightConjugateElem s (a : G) = t) :
    letI := unitAffineAction U
    MulAction.IsMultiplyPretransitive (unitAffineHom U u hu hcentral).range U 2 := by
  let := unitAffineAction U
  let := unitCoordinateAction U u
  have h := unitCoordinateAction_isTwoPretransitive U u htrans hstab
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨n, hn, hn'⟩ := MulAction.is_two_pretransitive_iff.mp h hab hcd
  refine ⟨⟨unitAffineHom U u hu hcentral n, n, rfl⟩, ?_, ?_⟩
  · change unitAffinePerm U (unitAffineHom U u hu hcentral n) a = c
    rw [unitAffineHom_action]
    exact hn
  · change unitAffinePerm U (unitAffineHom U u hu hcentral n) b = d
    rw [unitAffineHom_action]
    exact hn'

variable [Finite G]

theorem original_prescribed_sylow_full_conjugation_of_original_rank_data
    {H : Subgroup G} {z u : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type v) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (beta : pointRightCosetSpace H) (hb : beta ≠ rightCosetMk H 1)
    (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (huz : Commute u z) (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u))
    (hpairRank : twoRank (pairPointStabilizer H beta) ≤ 1)
    (T1 : Sylow 2 ↥(Subgroup.centralizer ({u} : Set G) ⊓ H)) :
    let M := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    let A := (T1 : Subgroup ↥(M ⊓ H)).map (M ⊓ H).subtype
    let T := A ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)))
    let Delta := involutionPointClass u ∩ (T : Set G)
    let N := Subgroup.normalizer Delta
    Delta = translatedCosetUnitSet H z u ∧
      (∀ s : G, s ∈ Delta → ∀ t : G, t ∈ Delta →
        ∃ n : N, rightConjugateElem s (n : G) = t) ∧
      (∀ s : G, s ∈ Delta → s ≠ u → ∀ t : G, t ∈ Delta → t ≠ u →
        ∃ a : (N ⊓ M : Subgroup G), rightConjugateElem s (a : G) = t) := by
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let A := (T1 : Subgroup ↥(M ⊓ H)).map (M ⊓ H).subtype
  let T := A ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)))
  have hcentral := original_local_hull_entire_oddCore_central
    h hcomm hsmallerR1 u hu huz hescape hrank
  obtain ⟨S0, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨_hmodel, _hcore, _hB, _hodd, _hfull, a, i, _ha, _hi, _hAt,
      helem, _hUle, hUset, _hq, _hfour, _hk, _hBindex, _e, _hbase, _he⟩ :=
    original_native_parameter_and_action_of_central_oddCore
      h.local_datum S0 hzS hzcenter u (pairPointStabilizer_le_point H beta huD)
      hu huz hescape hrank hcentral
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
  have hUT := original_root_le_supplied_sylow_of_complete_partition S hpartitionS
  obtain ⟨_hfused, hDeltaS⟩ := original_supplied_sylow_entire_class_intersection
    h beta hb huD hu huz hescape (originalPointRoot H z u) hUset helem S hUT hpartitionS
  have hDelta : involutionPointClass u ∩ (T : Set G) = translatedCosetUnitSet H z u := by
    rw [← hDeltaS, hS]
    exact original_class_intersection_eq_of_entire_involution_sets hu T A hproduct.2.1
  have hcoverage : ∀ x : G, x ∈ (S : Subgroup M).map M.subtype →
      IsInvolution x → x ∈ originalPointRoot H z u ∨
        x ∈ translatedCosetUnitSet H z u := by
    intro x hx hxI
    have hxorder : orderOf x = 2 := orderOf_eq_prime_iff.mpr ⟨hxI.2, hxI.1⟩
    have hxpartition := (Set.ext_iff.mp hpartitionS x).mp ⟨hx, hxorder⟩
    rcases hxpartition with (hxbase | hxroot) | hxtranslate
    · right
      rw [Set.mem_singleton_iff.mp hxbase]
      exact ⟨1, Or.inl (Set.mem_singleton 1), mul_one u⟩
    · exact Or.inl hxroot.1
    · right
      obtain ⟨w, hw, rfl⟩ := hxtranslate
      exact ⟨w, hUset ▸ hw.1, rfl⟩
  have hconj := original_coset_full_conjugation_of_supplied_sylow_geometry
    h beta hb huD hu huz hescape (originalPointRoot H z u) hUset S hcoverage hDeltaS
  dsimp only
  refine ⟨hDelta, ?_⟩
  rw [hDelta]
  exact ⟨hconj, original_coset_stabilizer_full_off_u_orbit h.local_datum hu huz hescape⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
