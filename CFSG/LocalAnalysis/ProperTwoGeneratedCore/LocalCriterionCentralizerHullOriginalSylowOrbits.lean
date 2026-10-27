module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullEveryOrbitAssembly
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullOriginalSylowProduct

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.BenderSuzuki.PFAppendixIII

universe v

variable {G : Type v} [Group G] [Finite G]

theorem original_hull_point_isStronglyEmbedded
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    let L := localInvolutionPointHull z u
    let M := Subgroup.centralizer ({u} : Set G)
    CFSG.BenderSuzuki.IsStronglyEmbedded ((L ⊓ (H ⊓ M)).subgroupOf L) := by
  let L := localInvolutionPointHull z u
  let M := Subgroup.centralizer ({u} : Set G)
  have hpoint : (L ⊓ (H ⊓ M)).subgroupOf L = H.subgroupOf L := by
    ext l
    change ((l : G) ∈ L ∧ (l : G) ∈ H ∧ (l : G) ∈ M) ↔ (l : G) ∈ H
    exact ⟨fun hl => hl.2.1,
      fun hl => ⟨l.property, hl, localInvolutionPointHull_le_centralizer z u l.property⟩⟩
  change CFSG.BenderSuzuki.IsStronglyEmbedded ((L ⊓ (H ⊓ M)).subgroupOf L)
  rw [hpoint]
  exact (h.local_embedding u hu huz hescape).to_native

theorem every_original_point_sylow_and_intersection_class_intersections
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (u : G) (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u))
    (hcentral : CFSG.oddCore (localInvolutionPointHull z u) ≤
      Subgroup.center (localInvolutionPointHull z u)) :
    let M := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    let U := originalPointRoot H z u
    ∀ T1 : Sylow 2 ↥(H ⊓ M),
      let T1' := (T1 : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype
      let T := T1' ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)))
      conjugacyWithin L u ∩ (T1' : Set G) = {u} ∧
      conjugacyWithin L z ∩ (T1' : Set G) = (U : Set G) \ {1} ∧
      conjugacyWithin L (u * z) ∩ (T1' : Set G) =
        (fun x : G => u * x) '' ((U : Set G) \ {1}) ∧
      conjugacyWithin L u ∩ (T : Set G) = {u} ∧
      conjugacyWithin L z ∩ (T : Set G) = (U : Set G) \ {1} ∧
      conjugacyWithin L (u * z) ∩ (T : Set G) =
        (fun x : G => u * x) '' ((U : Set G) \ {1}) := by
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let U := originalPointRoot H z u
  have huM : u ∈ M := Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl u).eq
  have huK : u ∈ Subgroup.centralizer (M : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro m hm
    exact Subgroup.mem_centralizer_singleton_iff.mp hm
  have huI : IsInvolution u :=
    ⟨(orderOf_eq_prime_iff.mp hu).2, (orderOf_eq_prime_iff.mp hu).1⟩
  have hzI : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).2,
      (orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).1⟩
  obtain ⟨helem, hUL, hUH, hnormal, hUset, _hfour, _hcard⟩ :=
    original_minimal_failure_whole_root_involution_data h u hu huz hescape hrank hcentral
  let := helem
  let := hnormal
  exact every_relative_point_sylow_and_intersection_class_intersections
    M L (H ⊓ M) U (localInvolutionPointHull_le_centralizer z u) inf_le_right
    (original_hull_point_isStronglyEmbedded h.local_datum u hu huz hescape)
    u z huI ⟨huH, huM⟩ huK (distinguished_mem_localInvolutionPointHull huz)
    ⟨h.local_datum.distinguished_mem, Subgroup.mem_centralizer_singleton_iff.mpr huz.symm⟩
    hzI hUL hUH hUset

theorem every_original_point_sylow_and_intersection_three_orbits :
    ∀ {H : Subgroup G} {z : G}, MinimalInvolutionPointLocalFailure H z →
    ∀ beta : pointRightCosetSpace H, beta ≠ rightCosetMk H 1 →
    twoRank (pairPointStabilizer H beta) ≤ 1 →
    ∀ u : G, u ∈ pairPointStabilizer H beta → orderOf u = 2 → Commute u z →
    (¬ Subgroup.centralizer ({u} : Set G) ≤ H) →
    2 ≤ twoRank (localInvolutionPointHull z u) →
    CFSG.oddCore (localInvolutionPointHull z u) ≤
      Subgroup.center (localInvolutionPointHull z u) →
    let M := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    let U := originalPointRoot H z u
    ∀ T1 : Sylow 2 ↥(H ⊓ M),
      let T1' := (T1 : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype
      let T := T1' ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)))
      let N := L ⊓ Subgroup.normalizer (U : Set G)
      let _ : MulAction N G := MulAction.compHom G
        (ConjAct.toConjAct.toMonoidHom.comp N.subtype)
      ∀ A : Subgroup G, A = T1' ∨ A = T →
        ∃ p : SubMulAction N G,
          (p : Set G) = {x : G | x ∈ A ∧ IsInvolution x} ∧
          ∃ a b c : p,
            (a : G) = u ∧ (b : G) = z ∧ (c : G) = u * z ∧
            Subtype.val '' MulAction.orbit N a = {u} ∧
            Subtype.val '' MulAction.orbit N b = (U : Set G) \ {1} ∧
            Subtype.val '' MulAction.orbit N c =
              (fun x : G => u * x) '' ((U : Set G) \ {1}) ∧
            (∀ x : p, x ∈ MulAction.orbit N a ∨
              x ∈ MulAction.orbit N b ∨ x ∈ MulAction.orbit N c) ∧
            Disjoint ({u} : Set G) ((U : Set G) \ {1}) ∧
            Disjoint ({u} : Set G)
              ((fun x : G => u * x) '' ((U : Set G) \ {1})) ∧
            Disjoint ((U : Set G) \ {1})
              ((fun x : G => u * x) '' ((U : Set G) \ {1})) ∧
            Set.range (fun q : MulAction.orbitRel.Quotient N p =>
              Subtype.val '' q.orbit) =
                {({u} : Set G), (U : Set G) \ {1},
                  (fun x : G => u * x) '' ((U : Set G) \ {1})} ∧
            Nat.card (MulAction.orbitRel.Quotient N p) = 3 := by
  intro H z h beta hbeta hpairRank u huD hu huz hescape hrank hcentral
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let U := originalPointRoot H z u
  dsimp only
  intro T1
  let T1' := (T1 : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype
  let T := T1' ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)))
  let N := L ⊓ Subgroup.normalizer (U : Set G)
  let _ : MulAction N G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp N.subtype)
  intro A hA
  have huH := pairPointStabilizer_le_point H beta huD
  have huM : u ∈ M := Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl u).eq
  have huK : u ∈ Subgroup.centralizer (M : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro m hm
    exact Subgroup.mem_centralizer_singleton_iff.mp hm
  have huI : IsInvolution u :=
    ⟨(orderOf_eq_prime_iff.mp hu).2, (orderOf_eq_prime_iff.mp hu).1⟩
  have hzI : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).2,
      (orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).1⟩
  obtain ⟨helem, hUL, hUH, hnormal, hUset, _hfour, _hcard⟩ :=
    original_minimal_failure_whole_root_involution_data h u hu huz hescape hrank hcentral
  let := helem
  let := hnormal
  obtain ⟨huL, hpartition⟩ := original_minimal_failure_entire_existential_involution_partition
    h beta hbeta hpairRank u huD hu huz hescape hrank
  exact every_relative_point_sylow_and_intersection_three_orbit_quotients
    M L (H ⊓ M) U (localInvolutionPointHull_le_centralizer z u) inf_le_right
    (original_hull_point_isStronglyEmbedded h.local_datum u hu huz hescape)
    u z huI ⟨huH, huM⟩ huK huL (distinguished_mem_localInvolutionPointHull huz)
    ⟨h.local_datum.distinguished_mem, Subgroup.mem_centralizer_singleton_iff.mpr huz.symm⟩
    hzI hUL hUH
    (original_minimal_failure_entire_point_index_and_oddness h u huH hu huz hescape hrank).2
    hUset hpartition T1 A hA

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
