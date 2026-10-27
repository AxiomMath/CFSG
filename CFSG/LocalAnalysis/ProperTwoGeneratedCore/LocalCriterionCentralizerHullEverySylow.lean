module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullProduct

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.BenderSuzuki.PFAppendixIII

universe u

variable {G : Type u} [Group G]

theorem normal_root_mem_every_point_sylow
    (H U : Subgroup G) (hUH : U ≤ H) [IsElementaryAbelian 2 U]
    [(U.subgroupOf H).Normal] (T : Sylow 2 H) :
    U ≤ (T : Subgroup H).map H.subtype := by
  let : IsElementaryAbelian 2 (U.subgroupOf H) := IsElementaryAbelian.subgroupOf hUH
  have hle : U.subgroupOf H ≤ (T : Subgroup H) :=
    (IsElementaryAbelian.isPGroup 2 (U.subgroupOf H)).le_sylow_of_normal T
  have hmap := Subgroup.map_mono (f := H.subtype) hle
  simpa only [Subgroup.map_subgroupOf_eq_of_le hUH] using hmap

theorem central_involution_mem_every_point_sylow
    (H : Subgroup G) (u : G) (huH : u ∈ H)
    (huZ : u ∈ Subgroup.center G) (hu : u ^ 2 = 1) (T : Sylow 2 H) :
    u ∈ (T : Subgroup H).map H.subtype := by
  have huHZ : (⟨u, huH⟩ : H) ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp huZ h
  have huHsq : (⟨u, huH⟩ : H) ^ 2 = 1 := Subtype.ext hu
  exact ⟨⟨u, huH⟩, central_square_one_mem_every_sylow _ huHZ huHsq T, rfl⟩

theorem entire_root_nonidentity_set
    (L H U : Subgroup G)
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ L ∧ x ∈ H ∧ IsInvolution x}) :
    (U : Set G) \ {1} = {x : G | x ∈ L ∧ x ∈ H ∧ IsInvolution x} := by
  ext x
  change (x ∈ (U : Set G) ∧ x ≠ 1) ↔ _
  rw [hU]
  constructor
  · rintro ⟨hx | hx, hxone⟩
    · exact (hxone hx).elim
    · exact hx
  · intro hx
    exact ⟨Or.inr hx, hx.2.2.ne_one⟩

theorem every_point_sylow_hull_intersection
    (L H U : Subgroup G) (hUL : U ≤ L) (hUH : U ≤ H)
    [IsElementaryAbelian 2 U] [(U.subgroupOf H).Normal]
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ L ∧ x ∈ H ∧ IsInvolution x})
    (T : Sylow 2 H) :
    (U : Set G) \ {1} =
      {x : G | x ∈ (T : Subgroup H).map H.subtype ∧ x ∈ L ∧ IsInvolution x} := by
  have hUT := normal_root_mem_every_point_sylow H U hUH T
  have hroot := entire_root_nonidentity_set L H U hU
  ext x
  constructor
  · intro hx
    have h := Set.ext_iff.mp hroot x |>.mp hx
    exact ⟨hUT hx.1, hUL hx.1, h.2.2⟩
  · rintro ⟨hxT, hxL, hx⟩
    exact Set.ext_iff.mp hroot x |>.mpr
      ⟨hxL, Subgroup.map_subtype_le (T : Subgroup H) hxT, hx⟩

theorem every_point_sylow_exact_product [Finite G]
    (L H U : Subgroup G) (u : G) (hu : IsInvolution u)
    (huZ : u ∈ Subgroup.center G) (huL : u ∉ L) (huH : u ∈ H)
    (hUL : U ≤ L) (hUH : U ≤ H) [IsElementaryAbelian 2 U]
    [(U.subgroupOf H).Normal] (hindex : Odd H.index)
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ L ∧ x ∈ H ∧ IsInvolution x})
    (hpartition : ∀ x : G, IsInvolution x →
      x = u ∨ x ∈ L ∨ ∃ l : G, l ∈ L ∧ IsInvolution l ∧ x = u * l) :
    ∀ T : Sylow 2 H,
      let T' := (T : Subgroup H).map H.subtype
      (∃ S : Sylow 2 G, (S : Subgroup G) = T') ∧
      {x : G | x ∈ T' ∧ IsInvolution x} =
        ({u} : Set G) ∪ ((U : Set G) \ {1}) ∪
          ((fun x : G => u * x) '' ((U : Set G) \ {1})) ∧
      (CFSG.omega₁ (G := T') (p := 2)).map T'.subtype = Subgroup.zpowers u ⊔ U ∧
      Disjoint (Subgroup.zpowers u) U ∧
      (∀ e ∈ Subgroup.zpowers u, ∀ k ∈ U, Commute e k) ∧
      IsElementaryAbelian 2 ↥(Subgroup.zpowers u ⊔ U : Subgroup G) ∧
      (∃ e : Subgroup.zpowers u × U ≃*
        ↥((CFSG.omega₁ (G := T') (p := 2)).map T'.subtype),
        ∀ (a : Subgroup.zpowers u) (b : U), (e (a, b) : G) = (a : G) * b) := by
  intro T
  let T' := (T : Subgroup H).map H.subtype
  have hUT : U ≤ T' := normal_root_mem_every_point_sylow H U hUH T
  have huT : u ∈ T' := central_involution_mem_every_point_sylow H u huH huZ hu.sq_eq_one T
  have hTH : T' ≤ H := Subgroup.map_subtype_le _
  have hInv := local_entire_involution_set L H U T' u hu huZ huL hUL hUT hTH huT hU hpartition
  have huU : u ∉ U := fun h => huL (hUL h)
  obtain ⟨hOmega, hdisj, hcomm, helem⟩ :=
    local_omega_one_internal_product U T' u hu huZ huU hUT huT hInv
  refine ⟨⟨sylowTwoOfOddIndex H hindex T, sylowTwoOfOddIndex_subgroup H hindex T⟩,
    hInv, hOmega, hdisj, hcomm, helem, ?_⟩
  exact local_omega_one_product_equivalence U T' u hOmega hdisj hcomm

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
