module

public import CFSG.LieType.ChevTwo.OppCl.Defs

public section

namespace CFSG.LieType.ChevTwo.OppCl.TK

open CFSG.Open CFSG.LieType.BorelTits

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {H : Type} [Group H]

theorem perm_apply_inv (r : Equiv.Perm V) (w : V) : r (r⁻¹ w) = w := r.apply_symm_apply w

theorem perm_inv_apply (r : Equiv.Perm V) (w : V) : r⁻¹ (r w) = w := r.symm_apply_apply w

theorem eq_of_forall_apply_perm {ρ : H →* Module.End F V} (hρ : Function.Injective ρ)
    (r : Equiv.Perm V) {a b : H} (h : ∀ v, ρ a (r v) = ρ b (r v)) : a = b := by
  refine hρ (LinearMap.ext fun w => ?_)
  have := h (r⁻¹ w)
  rwa [perm_apply_inv] at this

theorem semilin_map_add {r : Equiv.Perm V} (hr : r ∈ semilinGroup F V) (u v : V) :
    r (u + v) = r u + r v := hr.1 u v

theorem semilin_map_zero {r : Equiv.Perm V} (hr : r ∈ semilinGroup F V) : r 0 = 0 := by
  have h := hr.1 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem semilin_map_sub {r : Equiv.Perm V} (hr : r ∈ semilinGroup F V) (u v : V) :
    r (u - v) = r u - r v := by
  have h := hr.1 (u - v) v
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

end CFSG.LieType.ChevTwo.OppCl.TK
