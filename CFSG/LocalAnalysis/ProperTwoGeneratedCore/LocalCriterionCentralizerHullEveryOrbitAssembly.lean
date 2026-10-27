module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullRelativeIntersection
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullRelativeOrbits

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G]

theorem entire_root_intersection_of_subgroup_between
    (L H U T : Subgroup G) (hUL : U ≤ L) (hUT : U ≤ T) (hTH : T ≤ H)
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ L ∧ x ∈ H ∧ IsInvolution x}) :
    (U : Set G) \ {1} = {x : G | x ∈ T ∧ x ∈ L ∧ IsInvolution x} := by
  have hroot := entire_root_nonidentity_set L H U hU
  ext x
  constructor
  · intro hx
    have h := (Set.ext_iff.mp hroot x).mp hx
    exact ⟨hUT hx.1, hUL hx.1, h.2.2⟩
  · rintro ⟨hxT, hxL, hx⟩
    exact (Set.ext_iff.mp hroot x).mpr ⟨hxL, hTH hxT, hx⟩

theorem entire_root_as_hull_point_involution_set
    (L H U : Subgroup G)
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ L ∧ x ∈ H ∧ IsInvolution x}) :
    (U : Set G) = {1} ∪ {x : G | x ∈ L ⊓ H ∧ IsInvolution x} := by
  rw [hU]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq, Subgroup.mem_inf]
  tauto

theorem every_relative_point_sylow_and_intersection_class_intersections [Finite G]
    (M L H U : Subgroup G) (hLM : L ≤ M) (hHM : H ≤ M)
    (hP : IsStronglyEmbedded ((L ⊓ H).subgroupOf L))
    (u z : G) (hu : IsInvolution u) (huH : u ∈ H)
    (huK : u ∈ Subgroup.centralizer (M : Set G))
    (hzL : z ∈ L) (hzH : z ∈ H) (hz : IsInvolution z)
    (hUL : U ≤ L) (hUH : U ≤ H) [IsElementaryAbelian 2 U]
    [(U.subgroupOf H).Normal]
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ L ∧ x ∈ H ∧ IsInvolution x}) :
    ∀ T1 : Sylow 2 H,
      let T1' := (T1 : Subgroup H).map H.subtype
      let T := T1' ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)))
      conjugacyWithin L u ∩ (T1' : Set G) = {u} ∧
      conjugacyWithin L z ∩ (T1' : Set G) = (U : Set G) \ {1} ∧
      conjugacyWithin L (u * z) ∩ (T1' : Set G) =
        (fun x : G => u * x) '' ((U : Set G) \ {1}) ∧
      conjugacyWithin L u ∩ (T : Set G) = {u} ∧
      conjugacyWithin L z ∩ (T : Set G) = (U : Set G) \ {1} ∧
      conjugacyWithin L (u * z) ∩ (T : Set G) =
        (fun x : G => u * x) '' ((U : Set G) \ {1}) := by
  intro T1
  let T1' := (T1 : Subgroup H).map H.subtype
  let T := T1' ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)))
  have huLC : u ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.centralizer_le (show (L : Set G) ⊆ M from hLM) huK
  have hUT1 := normal_root_mem_every_point_sylow H U hUH T1
  have huT1 := relative_central_involution_mem_every_point_sylow
    M H hHM u huH huK hu.sq_eq_one T1
  have hT1H : T1' ≤ H := Subgroup.map_subtype_le _
  obtain ⟨hUT, huT⟩ := entire_root_and_involution_mem_literal_intersection
    M L U T1' hUL hUT1 u huT1 (hHM huH) huLC
  have hzU : z ∈ U := by
    change z ∈ (U : Set G)
    rw [hU]
    exact Or.inr ⟨hzL, hzH, hz⟩
  have hclass := entire_hull_involution_conjugacy_class L (L ⊓ H) hP z (hUL hzU) hz
  have hrootT1 := entire_root_intersection_of_subgroup_between L H U T1' hUL hUT1 hT1H hU
  have hrootT := entire_root_intersection_of_subgroup_between L H U T hUL hUT
    (inf_le_left.trans hT1H) hU
  have hfirst := relative_entire_class_intersections L U T1' u z
    hu.sq_eq_one huLC hUT1 huT1 hrootT1 hclass
  have hsecond := relative_entire_class_intersections L U T u z
    hu.sq_eq_one huLC hUT huT hrootT hclass
  exact ⟨hfirst.1, hfirst.2.1, hfirst.2.2, hsecond⟩

theorem every_relative_point_sylow_and_intersection_three_orbit_quotients [Finite G]
    (M L H U : Subgroup G) (hLM : L ≤ M) (hHM : H ≤ M)
    (hP : IsStronglyEmbedded ((L ⊓ H).subgroupOf L))
    (u z : G) (hu : IsInvolution u) (huH : u ∈ H)
    (huK : u ∈ Subgroup.centralizer (M : Set G)) (huL : u ∉ L)
    (hzL : z ∈ L) (hzH : z ∈ H) (hz : IsInvolution z)
    (hUL : U ≤ L) (hUH : U ≤ H) [IsElementaryAbelian 2 U]
    [(U.subgroupOf H).Normal] (hindex : Odd (H.subgroupOf M).index)
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ L ∧ x ∈ H ∧ IsInvolution x})
    (hpartition : ∀ x : G, x ∈ M → IsInvolution x →
      x = u ∨ x ∈ L ∨ ∃ l : G, l ∈ L ∧ IsInvolution l ∧ x = u * l) :
    ∀ T1 : Sylow 2 H,
      let T1' := (T1 : Subgroup H).map H.subtype
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
  intro T1
  let T1' := (T1 : Subgroup H).map H.subtype
  let T := T1' ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)))
  let N := L ⊓ Subgroup.normalizer (U : Set G)
  let _ : MulAction N G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp N.subtype)
  dsimp only
  intro A hA
  have huLC : u ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.centralizer_le (show (L : Set G) ⊆ M from hLM) huK
  have hroot := entire_root_as_hull_point_involution_set L H U hU
  have hInvT1 := (every_relative_point_sylow_exact_product M L H U hLM hHM u hu huH
    huK huL hUL hUH hindex hU hpartition T1).2.1
  have hInvT := (every_relative_point_sylow_literal_intersection_product M L H U hLM hHM
    u hu huH huK huL hUL hUH hindex hU hpartition T1).2.2.1
  have hInvA : {x : G | x ∈ A ∧ IsInvolution x} =
      ({u} : Set G) ∪ ((U : Set G) \ {1}) ∪
        ((fun x : G => u * x) '' ((U : Set G) \ {1})) := by
    rcases hA with rfl | rfl
    · exact hInvT1
    · exact hInvT
  exact relative_entire_local_three_conjugation_orbits L (L ⊓ H) U A inf_le_left
    hP hroot u z huLC huL ⟨hzL, hzH⟩ hz hInvA

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
