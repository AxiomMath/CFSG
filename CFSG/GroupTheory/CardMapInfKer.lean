module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG

theorem card_map_eq_card_of_inf_ker_eq_bot {G H : Type*} [Group G] [Group H] (f : G →* H)
    {J : Subgroup G} (h : J ⊓ f.ker = ⊥) : Nat.card ↥(J.map f) = Nat.card ↥J := by
  have hker : (f.comp J.subtype).ker = ⊥ := by
    change (f.domRestrict J).ker = ⊥
    rw [MonoidHom.ker_domRestrict, Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_comm]
    exact h
  have hinj : Function.Injective (f.comp J.subtype) := (MonoidHom.ker_eq_bot_iff _).1 hker
  have hrange : (f.comp J.subtype).range = J.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end CFSG

end
