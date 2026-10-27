module

public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.EvenSporadicStandard.Induction.AutBound

open Subgroup

theorem injective_and_range_of_card_le {G P : Type*} [Group G] [Finite G] [Group P] (π : G →* P)
    (S : Set G) (h : Nat.card G ≤ Nat.card ↥(closure (π '' S))) :
    closure S = ⊤ ∧ Function.Injective π ∧ π.range = closure (π '' S) := by
  have hmap : (closure S).map π = closure (π '' S) := MonoidHom.map_closure π S
  have h1 : Nat.card ↥((closure S).map π) ≤ Nat.card ↥(closure S) :=
    Nat.card_le_card_of_surjective _ (π.subgroupMap_surjective (closure S))
  have h2 : Nat.card ↥(closure S) ≤ Nat.card G := Subgroup.card_le_card_group _
  rw [hmap] at h1
  have h3 : Nat.card ↥(closure S) = Nat.card G := le_antisymm h2 (h.trans h1)
  have hS : closure S = ⊤ := (Subgroup.card_eq_iff_eq_top _).1 h3
  have hbij : Function.Bijective (π.subgroupMap (closure S)) :=
    (π.subgroupMap_surjective (closure S)).bijective_of_nat_card_le (by
      rw [hmap]
      exact h3 ▸ h)
  refine ⟨hS, fun x y hxy => ?_, ?_⟩
  · have hx : x ∈ closure S := hS ▸ Subgroup.mem_top x
    have hy : y ∈ closure S := hS ▸ Subgroup.mem_top y
    have := hbij.1 (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext hxy)
    exact congrArg Subtype.val this
  · rw [MonoidHom.range_eq_map, ← hS, hmap]

end CFSG.EvenSporadicStandard.Induction.AutBound
