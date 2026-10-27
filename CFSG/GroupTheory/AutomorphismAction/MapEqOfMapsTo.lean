module

public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.GroupTheory

theorem map_eq_of_mapsTo {G : Type*} [Group G] {H : Subgroup G} [Finite H]
    (e : MulAut G) (h : ∀ x ∈ H, e x ∈ H) : H.map e.toMonoidHom = H :=
  Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)
    (Subgroup.card_map_of_injective e.injective).ge

theorem apply_mem_iff_of_mapsTo {G : Type*} [Group G] {H : Subgroup G} [Finite H]
    (e : MulAut G) (h : ∀ x ∈ H, e x ∈ H) (x : G) : e x ∈ H ↔ x ∈ H := by
  conv_lhs => rw [← map_eq_of_mapsTo e h]
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

end CFSG.GroupTheory
