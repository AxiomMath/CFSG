module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullOriginalSylowOrbits

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.BenderSuzuki.PFAppendixIII

universe v

variable {G : Type v} [Group G]

theorem conjugacyWithin_le_entire_global_class (A : Subgroup G) (x : G) :
    conjugacyWithin A x ⊆ involutionPointClass x := by
  rintro y ⟨a, hay⟩
  exact ⟨a, hay⟩

variable [Finite G]

theorem original_minimal_failure_entire_centralizer_three_hull_classes
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) ≤ 1)
    (u : G) (huD : u ∈ pairPointStabilizer H beta)
    (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let M := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    conjugacyWithin L u = {u} ∧
      conjugacyWithin L z = {x : G | x ∈ L ∧ IsInvolution x} ∧
      conjugacyWithin L (u * z) =
        (fun x : G => u * x) '' {x : G | x ∈ L ∧ IsInvolution x} ∧
      {x : G | x ∈ M ∧ IsInvolution x} =
        conjugacyWithin L u ∪ conjugacyWithin L z ∪ conjugacyWithin L (u * z) ∧
      Disjoint (conjugacyWithin L u) (conjugacyWithin L z) ∧
      Disjoint (conjugacyWithin L u) (conjugacyWithin L (u * z)) ∧
      Disjoint (conjugacyWithin L z) (conjugacyWithin L (u * z)) := by
  let L := localInvolutionPointHull z u
  let M := Subgroup.centralizer ({u} : Set G)
  have huLC : u ∈ Subgroup.centralizer (L : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (localInvolutionPointHull_le_centralizer z u hl)
  have hzI : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).2,
      (orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).1⟩
  have hCu := centralizer_singleton_conjugacy_class L u huLC
  have hCz := entire_hull_involution_conjugacy_class L (L ⊓ (H ⊓ M))
    (original_hull_point_isStronglyEmbedded h.local_datum u hu huz hescape)
    z (distinguished_mem_localInvolutionPointHull huz) hzI
  have hCuz : conjugacyWithin L (u * z) =
      (fun x : G => u * x) '' {x : G | x ∈ L ∧ IsInvolution x} := by
    rw [centralizer_translate_conjugacy_class L u z huLC, hCz]
  have hpartition := original_minimal_failure_pair_centralizer_involution_partition
    h beta hbeta hpairRank u huD hu huz hescape hrank
  refine ⟨hCu, hCz, hCuz, ?_, ?_, ?_, ?_⟩
  · rw [hCu, hCz, hCuz]
    exact hpartition.2.2.1
  · rw [hCu, hCz]
    exact hpartition.2.2.2.1
  · rw [hCu, hCuz]
    exact hpartition.2.2.2.2.1
  · rw [hCz, hCuz]
    exact hpartition.2.2.2.2.2

theorem original_minimal_failure_entire_centralizer_three_conjugation_orbits
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) ≤ 1)
    (u : G) (huD : u ∈ pairPointStabilizer H beta)
    (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let M := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    let _ : MulAction L G := MulAction.compHom G
      (ConjAct.toConjAct.toMonoidHom.comp L.subtype)
    ∃ p : SubMulAction L G,
      (p : Set G) = {x : G | x ∈ M ∧ IsInvolution x} ∧
      ∃ a b c : p,
        (a : G) = u ∧ (b : G) = z ∧ (c : G) = u * z ∧
        Subtype.val '' MulAction.orbit L a = conjugacyWithin L u ∧
        Subtype.val '' MulAction.orbit L b = conjugacyWithin L z ∧
        Subtype.val '' MulAction.orbit L c = conjugacyWithin L (u * z) ∧
        (∀ x : p, x ∈ MulAction.orbit L a ∨
          x ∈ MulAction.orbit L b ∨ x ∈ MulAction.orbit L c) ∧
        Set.range (fun q : MulAction.orbitRel.Quotient L p =>
          Subtype.val '' q.orbit) =
            {conjugacyWithin L u, conjugacyWithin L z, conjugacyWithin L (u * z)} ∧
        Nat.card (MulAction.orbitRel.Quotient L p) = 3 := by
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let _ : MulAction L G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp L.subtype)
  obtain ⟨_hCu, _hCz, _hCuz, hwhole, hd1, hd2, hd3⟩ :=
    original_minimal_failure_entire_centralizer_three_hull_classes
      h beta hbeta hpairRank u huD hu huz hescape hrank
  have hOu := conjugation_orbit_eq_conjugacyWithin L u
  have hOz := conjugation_orbit_eq_conjugacyWithin L z
  have hOuz := conjugation_orbit_eq_conjugacyWithin L (u * z)
  have hcover : {x : G | x ∈ M ∧ IsInvolution x} =
      MulAction.orbit L u ∪ MulAction.orbit L z ∪ MulAction.orbit L (u * z) := by
    rw [hOu, hOz, hOuz]
    exact hwhole
  obtain ⟨p, hp, a, b, c, ha, hb, hc, hIa, hIb, hIc, hfull, hrange, hcount⟩ :=
    entire_three_orbit_carrier _ u z (u * z) hcover
      (by rw [hOu, hOz]; exact hd1)
      (by rw [hOu, hOuz]; exact hd2)
      (by rw [hOz, hOuz]; exact hd3)
  rw [hOu] at hIa
  rw [hOz] at hIb
  rw [hOuz] at hIc
  rw [hOu, hOz, hOuz] at hrange
  exact ⟨p, hp, a, b, c, ha, hb, hc, hIa, hIb, hIc, hfull, hrange, hcount⟩

theorem original_minimal_failure_whole_root_global_class_inclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u))
    (hcentral : CFSG.oddCore (localInvolutionPointHull z u) ≤
      Subgroup.center (localInvolutionPointHull z u)) :
    let U := originalPointRoot H z u
    (U : Set G) \ {1} ⊆ involutionPointClass z ∧
      (fun x : G => u * x) '' ((U : Set G) \ {1}) ⊆ involutionPointClass (u * z) := by
  let L := localInvolutionPointHull z u
  let M := Subgroup.centralizer ({u} : Set G)
  let U := originalPointRoot H z u
  obtain ⟨_helem, _hUL, _hUH, _hnormal, hUset, _hfour, _hcard⟩ :=
    original_minimal_failure_whole_root_involution_data h u hu huz hescape hrank hcentral
  have hzI : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).2,
      (orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).1⟩
  have hclass := entire_hull_involution_conjugacy_class L (L ⊓ (H ⊓ M))
    (original_hull_point_isStronglyEmbedded h.local_datum u hu huz hescape)
    z (distinguished_mem_localInvolutionPointHull huz) hzI
  have hrootclass : (U : Set G) \ {1} ⊆ conjugacyWithin L z := by
    rintro x ⟨hxU, hxone⟩
    rw [hUset] at hxU
    rcases hxU with hx | hx
    · exact (hxone hx).elim
    · exact hclass.symm ▸ ⟨hx.1, hx.2.2⟩
  have huLC : u ∈ Subgroup.centralizer (L : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (localInvolutionPointHull_le_centralizer z u hl)
  refine ⟨hrootclass.trans (conjugacyWithin_le_entire_global_class L z), ?_⟩
  have htranslate : (fun x : G => u * x) '' ((U : Set G) \ {1}) ⊆
      conjugacyWithin L (u * z) := by
    rw [centralizer_translate_conjugacy_class L u z huLC]
    exact Set.image_mono hrootclass
  exact htranslate.trans (conjugacyWithin_le_entire_global_class L (u * z))

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
