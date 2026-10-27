module

public import CFSG.GroupTheory.WielandtProductAux

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

private theorem exists_ne_one_commute_of_isPGroup {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : IsPGroup p P) (hPne : P ≠ ⊥) {g : G} (hg : IsPGroup p (Subgroup.zpowers g))
    (hnorm : g ∈ Subgroup.normalizer (P : Set G)) :
    ∃ x ∈ P, x ≠ 1 ∧ g * x = x * g := by
  have hz : Subgroup.zpowers g ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le.mpr hnorm
  obtain ⟨x, hxP, hx1, hxcomm⟩ :=
    WielandtProduct.exists_mem_commute_of_le_of_isPGroup
      (p := p) (P := P ⊔ Subgroup.zpowers g) (N := P)
      (hP.to_sup_of_normal_left' hg hz) le_sup_left
      (sup_le Subgroup.le_normalizer hz) hPne
  exact ⟨x, hxP, hx1,
    (hxcomm g (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))).symm⟩

end CFSG.GroupTheory
