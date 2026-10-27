module


public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.FiniteMinimalSubgroup

theorem exists_minimal_subgroup {G : Type*} [Group G] [Finite G] (P : Subgroup G → Prop)
    (h : ∃ V, P V) : ∃ V, P V ∧ ∀ W, P W → W ≤ V → W = V := by
  have exists_minimal_subgroup' (P : Subgroup G → Prop)
      (h : ∃ V, P V) : ∃ V, Minimal P V := by
    have : Finite (Subgroup G) := Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
    obtain ⟨V, hV⟩ := h
    exact (Set.toFinite {W | P W}).exists_minimal ⟨V, hV⟩ |>.imp fun W hW => hW
  obtain ⟨V, hV⟩ := exists_minimal_subgroup' P h
  exact ⟨V, hV.prop, fun W hW hle => le_antisymm hle (hV.2 hW hle)⟩

end CFSG.GroupTheory.CoprimeActionSupport.FiniteMinimalSubgroup
