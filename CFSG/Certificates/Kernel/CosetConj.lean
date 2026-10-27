module

public import Mathlib.Data.List.Nodup
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.KC.CosetConj

variable {G : Type*} [Group G]

theorem perm_map_mul {C : Subgroup G} {L : List G} (hL : L.Nodup) (hm : ∀ g, g ∈ L ↔ g ∈ C)
    {κ : G} (hκ : κ ∈ C) : (L.map (κ * ·)).Perm L := by
  rw [List.perm_ext_iff_of_nodup (List.Nodup.map (mul_right_injective κ) hL) hL]
  intro x
  rw [List.mem_map, hm]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact C.mul_mem hκ ((hm g).1 hg)
  · intro hx
    exact ⟨κ⁻¹ * x, (hm _).2 (C.mul_mem (C.inv_mem hκ) hx), by rw [mul_inv_cancel_left]⟩

theorem countP_mul_eq {C : Subgroup G} {L : List G} (hL : L.Nodup) (hm : ∀ g, g ∈ L ↔ g ∈ C)
    (F : G → Bool) {ρ ν : G} (hκ : ν⁻¹ * ρ ∈ C) (hF : ∀ g ∈ C, F (ν * g) = F g) :
    L.countP (fun g => F (ρ * g)) = L.countP F := by
  have e : (fun g => F (ρ * g)) = (fun g => F (ν * g)) ∘ ((ν⁻¹ * ρ) * ·) := by
    funext g
    rw [Function.comp_apply, ← mul_assoc, mul_inv_cancel_left]
  rw [e, ← List.countP_map, (perm_map_mul hL hm hκ).countP_eq]
  exact List.countP_congr fun g hg => by rw [hF g ((hm g).1 hg)]

end CFSG.KC.CosetConj

end
