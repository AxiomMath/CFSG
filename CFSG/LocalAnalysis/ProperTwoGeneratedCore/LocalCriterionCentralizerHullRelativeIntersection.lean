module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullRelativeSylow

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.BenderSuzuki.PFAppendixIII
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem hull_relative_centralizer_product_carrier (M L : Subgroup G) :
    ((L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)) : Subgroup G) : Set G) =
      (L : Set G) * ((M ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  let K := M ⊓ Subgroup.centralizer (L : Set G)
  have hLC : L ≤ Subgroup.centralizer (K : Set G) := by
    intro l hl
    apply Subgroup.mem_centralizer_iff.mpr
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp hk.2 l hl).symm
  exact Subgroup.coe_mul_of_left_le_normalizer_right L K
    (hLC.trans (Subgroup.centralizer_le_normalizer _))

theorem entire_involutions_mem_hull_relative_centralizer_product
    (M L : Subgroup G) (u : G) (huM : u ∈ M)
    (huK : u ∈ Subgroup.centralizer (L : Set G))
    (hpartition : ∀ x : G, x ∈ M → IsInvolution x →
      x = u ∨ x ∈ L ∨ ∃ l : G, l ∈ L ∧ IsInvolution l ∧ x = u * l) :
    ∀ x : G, x ∈ M → IsInvolution x →
      x ∈ L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)) := by
  intro x hxM hx
  have hujoin : u ∈ L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)) :=
    Subgroup.mem_sup_right ⟨huM, huK⟩
  rcases hpartition x hxM hx with rfl | hxL | ⟨l, hlL, _hl, rfl⟩
  · exact hujoin
  · exact Subgroup.mem_sup_left hxL
  · exact Subgroup.mul_mem _ hujoin (Subgroup.mem_sup_left hlL)

theorem literal_hull_centralizer_intersection_involution_set
    (M L T1 : Subgroup G) (hT1M : T1 ≤ M)
    (u : G) (huM : u ∈ M) (huK : u ∈ Subgroup.centralizer (L : Set G))
    (hpartition : ∀ x : G, x ∈ M → IsInvolution x →
      x = u ∨ x ∈ L ∨ ∃ l : G, l ∈ L ∧ IsInvolution l ∧ x = u * l) :
    {x : G | x ∈ T1 ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G))) ∧ IsInvolution x} =
      {x : G | x ∈ T1 ∧ IsInvolution x} := by
  ext x
  constructor
  · rintro ⟨hxT, hx⟩
    exact ⟨hxT.1, hx⟩
  · rintro ⟨hxT, hx⟩
    exact ⟨⟨hxT, entire_involutions_mem_hull_relative_centralizer_product
      M L u huM huK hpartition x (hT1M hxT) hx⟩, hx⟩

theorem literal_hull_centralizer_intersection_omega_one
    (M L T1 : Subgroup G) (hT1M : T1 ≤ M)
    (u : G) (huM : u ∈ M) (huK : u ∈ Subgroup.centralizer (L : Set G))
    (hpartition : ∀ x : G, x ∈ M → IsInvolution x →
      x = u ∨ x ∈ L ∨ ∃ l : G, l ∈ L ∧ IsInvolution l ∧ x = u * l) :
    let T := T1 ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)))
    (CFSG.omega₁ (G := T) (p := 2)).map T.subtype =
      (CFSG.omega₁ (G := T1) (p := 2)).map T1.subtype := by
  dsimp only
  rw [omega_one_map_eq_entire_involution_closure,
    literal_hull_centralizer_intersection_involution_set M L T1 hT1M u huM huK hpartition,
    omega_one_map_eq_entire_involution_closure]

theorem entire_root_and_involution_mem_literal_intersection
    (M L U T1 : Subgroup G) (hUL : U ≤ L) (hUT1 : U ≤ T1)
    (u : G) (huT1 : u ∈ T1) (huM : u ∈ M)
    (huK : u ∈ Subgroup.centralizer (L : Set G)) :
    U ≤ T1 ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G))) ∧
      u ∈ T1 ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G))) := by
  exact ⟨fun x hx => ⟨hUT1 hx, Subgroup.mem_sup_left (hUL hx)⟩,
    huT1, Subgroup.mem_sup_right ⟨huM, huK⟩⟩

theorem every_relative_point_sylow_literal_intersection_product [Finite G]
    (M L H U : Subgroup G) (hLM : L ≤ M) (hHM : H ≤ M)
    (u : G) (hu : IsInvolution u) (huH : u ∈ H)
    (huK : u ∈ Subgroup.centralizer (M : Set G)) (huL : u ∉ L)
    (hUL : U ≤ L) (hUH : U ≤ H) [IsElementaryAbelian 2 U]
    [(U.subgroupOf H).Normal] (hindex : Odd (H.subgroupOf M).index)
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ L ∧ x ∈ H ∧ IsInvolution x})
    (hpartition : ∀ x : G, x ∈ M → IsInvolution x →
      x = u ∨ x ∈ L ∨ ∃ l : G, l ∈ L ∧ IsInvolution l ∧ x = u * l) :
    ∀ T1 : Sylow 2 H,
      let T1' := (T1 : Subgroup H).map H.subtype
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
  intro T1
  let T1' := (T1 : Subgroup H).map H.subtype
  let T := T1' ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)))
  obtain ⟨hSylow, hInv, hOmega, _hInside, hdisj, hcomm, helem, _hequiv⟩ :=
    every_relative_point_sylow_exact_product M L H U hLM hHM u hu huH huK huL
      hUL hUH hindex hU hpartition T1
  have huLC : u ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.centralizer_le (show (L : Set G) ⊆ M from hLM) huK
  have hT1M : T1' ≤ M := (Subgroup.map_subtype_le _).trans hHM
  have hInvSame := literal_hull_centralizer_intersection_involution_set
    M L T1' hT1M u (hHM huH) huLC hpartition
  have hOmegaSame := literal_hull_centralizer_intersection_omega_one
    M L T1' hT1M u (hHM huH) huLC hpartition
  have hOmegaT : (CFSG.omega₁ (G := T) (p := 2)).map T.subtype = Subgroup.zpowers u ⊔ U :=
    hOmegaSame.trans hOmega
  exact ⟨hSylow, hInvSame, hInvSame.trans hInv, hOmegaSame, hOmegaT,
    literal_omega_one_eq_subgroupOf_product U T u hOmegaT, hdisj, hcomm, helem,
    local_omega_one_product_equivalence U T u hOmegaT hdisj hcomm⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
