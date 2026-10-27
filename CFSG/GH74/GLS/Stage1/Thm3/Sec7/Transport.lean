module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.Tr

variable {G Gs : Type*} [Group G] [Group Gs]

structure FHom (S : Subgroup G) (f : G → Gs) : Prop where
  mul : ∀ a ∈ S, ∀ b ∈ S, f (a * b) = f a * f b
  inj : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b

namespace FHom

variable {S : Subgroup G} {f : G → Gs}

theorem map_one (hf : FHom S f) : f 1 = 1 := by
  have h := hf.mul 1 S.one_mem 1 S.one_mem
  rw [mul_one] at h
  exact left_eq_mul.1 h

theorem map_inv (hf : FHom S f) {a : G} (ha : a ∈ S) : f a⁻¹ = (f a)⁻¹ := by
  have h := hf.mul a ha a⁻¹ (S.inv_mem ha)
  rw [mul_inv_cancel, hf.map_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem map_conj (hf : FHom S f) {c v : G} (hc : c ∈ S) (hv : v ∈ S) :
    f (c * v * c⁻¹) = f c * f v * (f c)⁻¹ := by
  rw [hf.mul (c * v) (S.mul_mem hc hv) c⁻¹ (S.inv_mem hc), hf.mul c hc v hv, hf.map_inv hc]

theorem ne_one (hf : FHom S f) {a : G} (ha : a ∈ S) (h1 : a ≠ 1) : f a ≠ 1 := by
  intro h
  exact h1 (hf.inj a ha 1 S.one_mem (h.trans hf.map_one.symm))

theorem orderOf_eq_two (hf : FHom S f) {v : G} (hv : v ∈ S) (hv2 : orderOf v = 2) :
    orderOf (f v) = 2 := by
  have h1 : v ≠ 1 := fun h => by simp [h] at hv2
  have h2 : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rw [hv2, pow_two] at this
    exact this
  refine orderOf_eq_prime (p := 2) ?_ (hf.ne_one hv h1)
  rw [pow_two, ← hf.mul v hv v hv, h2, hf.map_one]

end FHom

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.Tr
