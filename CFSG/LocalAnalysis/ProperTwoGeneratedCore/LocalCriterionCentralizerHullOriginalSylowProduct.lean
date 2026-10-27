module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullOriginalPointSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullOriginalRootInvolutions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullRelativeIntersection
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairPartition

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.BenderSuzuki.PFAppendixIII

universe v

variable {G : Type v} [Group G] [Finite G]

theorem original_minimal_failure_entire_existential_involution_partition
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) ≤ 1)
    (u : G) (huD : u ∈ pairPointStabilizer H beta)
    (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let M := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    u ∉ L ∧ ∀ x : G, x ∈ M → IsInvolution x →
      x = u ∨ x ∈ L ∨ ∃ l : G, l ∈ L ∧ IsInvolution l ∧ x = u * l := by
  have hfull := original_minimal_failure_pair_centralizer_involution_partition
    h beta hbeta hpairRank u huD hu huz hescape hrank
  refine ⟨hfull.1, ?_⟩
  intro x hxM hx
  have hxset := (Set.ext_iff.mp hfull.2.2.1 x).mp ⟨hxM, hx⟩
  rcases hxset with (hxu | hxL) | ⟨l, hl, hxl⟩
  · exact Or.inl hxu
  · exact Or.inr (Or.inl hxL.1)
  · exact Or.inr (Or.inr ⟨l, hl.1, hl.2, hxl.symm⟩)

theorem every_original_point_sylow_entire_involutions_and_product
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) ≤ 1)
    (u : G) (huD : u ∈ pairPointStabilizer H beta)
    (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u))
    (hcentral : CFSG.oddCore (localInvolutionPointHull z u) ≤
      Subgroup.center (localInvolutionPointHull z u)) :
    let M := Subgroup.centralizer ({u} : Set G)
    let U := originalPointRoot H z u
    ∀ T1 : Sylow 2 ↥(H ⊓ M),
      let T1' := (T1 : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype
      (∃ S : Sylow 2 M, (S : Subgroup M).map M.subtype = T1') ∧
      {x : G | x ∈ T1' ∧ IsInvolution x} =
        ({u} : Set G) ∪ ((U : Set G) \ {1}) ∪
          ((fun x : G => u * x) '' ((U : Set G) \ {1})) ∧
      (CFSG.omega₁ (G := T1') (p := 2)).map T1'.subtype = Subgroup.zpowers u ⊔ U ∧
      CFSG.omega₁ (G := T1') (p := 2) = (Subgroup.zpowers u ⊔ U).subgroupOf T1' ∧
      Disjoint (Subgroup.zpowers u) U ∧
      (∀ e ∈ Subgroup.zpowers u, ∀ k ∈ U, Commute e k) ∧
      IsElementaryAbelian 2 ↥(Subgroup.zpowers u ⊔ U : Subgroup G) ∧
      (∃ e : Subgroup.zpowers u × U ≃*
        ↥((CFSG.omega₁ (G := T1') (p := 2)).map T1'.subtype),
        ∀ (a : Subgroup.zpowers u) (b : U), (e (a, b) : G) = (a : G) * b) := by
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let U := originalPointRoot H z u
  have huH := pairPointStabilizer_le_point H beta huD
  have huM : u ∈ M := Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl u).eq
  have huK : u ∈ Subgroup.centralizer (M : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro m hm
    exact Subgroup.mem_centralizer_singleton_iff.mp hm
  have huI : IsInvolution u :=
    ⟨(orderOf_eq_prime_iff.mp hu).2, (orderOf_eq_prime_iff.mp hu).1⟩
  obtain ⟨helem, hUL, hUH, hnormal, hUset, _hfour, _hcard⟩ :=
    original_minimal_failure_whole_root_involution_data h u hu huz hescape hrank hcentral
  let := helem
  let := hnormal
  obtain ⟨huL, hpartition⟩ := original_minimal_failure_entire_existential_involution_partition
    h beta hbeta hpairRank u huD hu huz hescape hrank
  exact every_relative_point_sylow_exact_product M L (H ⊓ M) U
    (localInvolutionPointHull_le_centralizer z u) inf_le_right u huI ⟨huH, huM⟩
    huK huL hUL hUH
    (original_minimal_failure_entire_point_index_and_oddness h u huH hu huz hescape hrank).2
    hUset hpartition

theorem every_original_point_sylow_literal_intersection_entire_product
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) ≤ 1)
    (u : G) (huD : u ∈ pairPointStabilizer H beta)
    (hu : orderOf u = 2) (huz : Commute u z)
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
      (∃ S : Sylow 2 M, (S : Subgroup M).map M.subtype = T1') ∧
      {x : G | x ∈ T ∧ IsInvolution x} = {x : G | x ∈ T1' ∧ IsInvolution x} ∧
      {x : G | x ∈ T ∧ IsInvolution x} =
        ({u} : Set G) ∪ ((U : Set G) \ {1}) ∪
          ((fun x : G => u * x) '' ((U : Set G) \ {1})) ∧
      (CFSG.omega₁ (G := T) (p := 2)).map T.subtype =
        (CFSG.omega₁ (G := T1') (p := 2)).map T1'.subtype ∧
      (CFSG.omega₁ (G := T) (p := 2)).map T.subtype = Subgroup.zpowers u ⊔ U ∧
      CFSG.omega₁ (G := T) (p := 2) = (Subgroup.zpowers u ⊔ U).subgroupOf T ∧
      Disjoint (Subgroup.zpowers u) U ∧
      (∀ e ∈ Subgroup.zpowers u, ∀ k ∈ U, Commute e k) ∧
      IsElementaryAbelian 2 ↥(Subgroup.zpowers u ⊔ U : Subgroup G) ∧
      (∃ e : Subgroup.zpowers u × U ≃*
        ↥((CFSG.omega₁ (G := T) (p := 2)).map T.subtype),
        ∀ (a : Subgroup.zpowers u) (b : U), (e (a, b) : G) = (a : G) * b) := by
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let U := originalPointRoot H z u
  have huH := pairPointStabilizer_le_point H beta huD
  have huM : u ∈ M := Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl u).eq
  have huK : u ∈ Subgroup.centralizer (M : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro m hm
    exact Subgroup.mem_centralizer_singleton_iff.mp hm
  have huI : IsInvolution u :=
    ⟨(orderOf_eq_prime_iff.mp hu).2, (orderOf_eq_prime_iff.mp hu).1⟩
  obtain ⟨helem, hUL, hUH, hnormal, hUset, _hfour, _hcard⟩ :=
    original_minimal_failure_whole_root_involution_data h u hu huz hescape hrank hcentral
  let := helem
  let := hnormal
  obtain ⟨huL, hpartition⟩ := original_minimal_failure_entire_existential_involution_partition
    h beta hbeta hpairRank u huD hu huz hescape hrank
  exact every_relative_point_sylow_literal_intersection_product M L (H ⊓ M) U
    (localInvolutionPointHull_le_centralizer z u) inf_le_right u huI ⟨huH, huM⟩
    huK huL hUL hUH
    (original_minimal_failure_entire_point_index_and_oddness h u huH hu huz hescape hrank).2
    hUset hpartition

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
