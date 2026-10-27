module

public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.GroupTheory

theorem center_eq_bot_of_le_of_centralizer_eq_bot {G : Type*} [Group G] {L H : Subgroup G}
    (hLH : L ≤ H) (hC : Subgroup.centralizer (L : Set G) = ⊥) :
    Subgroup.center ↥H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hzC : (z : G) ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨y, hLH hy⟩)
  rw [hC, Subgroup.mem_bot] at hzC
  exact Subgroup.mem_bot.2 (Subtype.ext hzC)

end CFSG.GroupTheory
