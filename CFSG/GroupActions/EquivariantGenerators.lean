module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.GroupActions

theorem injective_of_equivariant_on_generators {G H α β : Type*} [Group G] [Group H]
    (S : Set G) (hS : Subgroup.closure S = ⊤) (φ : G →* H)
    (σ : G →* Equiv.Perm α) (hσ : Function.Injective σ)
    (τ : H →* Equiv.Perm β) (e : α → β) (he : Function.Injective e)
    (hgen : ∀ s ∈ S, ∀ x, τ (φ s) (e x) = e (σ s x)) : Function.Injective φ := by
  let K : Subgroup G :=
    { carrier := {g | ∀ x, τ (φ g) (e x) = e (σ g x)}
      one_mem' := fun x => by simp
      mul_mem' := fun {g h} hg hh x => by
        simp only [Set.mem_setOf_eq, map_mul, Equiv.Perm.mul_apply] at hg hh ⊢
        rw [hh x, hg]
      inv_mem' := fun {g} hg x => by
        simp only [Set.mem_setOf_eq, map_inv] at hg ⊢
        have h := hg ((σ g)⁻¹ x)
        rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at h
        rw [Equiv.Perm.inv_eq_iff_eq, h] }
  have hK : Subgroup.closure S ≤ K := (Subgroup.closure_le K).mpr hgen
  have hall : ∀ g x, τ (φ g) (e x) = e (σ g x) := fun g =>
    hK (hS ▸ Subgroup.mem_top g)
  rw [injective_iff_map_eq_one]
  intro g hg
  apply hσ
  rw [map_one]
  ext x
  have h := hall g x
  rw [hg, map_one, Equiv.Perm.one_apply] at h
  exact (he h).symm

end CFSG.GroupActions
