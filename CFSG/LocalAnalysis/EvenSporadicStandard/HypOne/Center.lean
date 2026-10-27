module

public import Mathlib.GroupTheory.Subgroup.Center

public section

namespace CFSG.EvenSporadicStandard.HypOne

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center X = ⊥) : Subgroup.center Y = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hx : e.symm y ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy (e g)
  rw [h, Subgroup.mem_bot] at hx
  rw [Subgroup.mem_bot, ← MulEquiv.apply_symm_apply e y, hx, map_one]

end CFSG.EvenSporadicStandard.HypOne
