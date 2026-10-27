module

public import CFSG.GH74.GLS.Bg.TwoGroups.Vocab

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open CFSG.GH74.GLS.Bg.TwoGroups

@[expose] def fixSub {T : Type*} [Group T] (α : MulAut T) : Subgroup T where
  carrier := {g | α g = g}
  mul_mem' := by
    intro a b ha hb
    change α a = a at ha
    change α b = b at hb
    change α (a * b) = a * b
    rw [map_mul, ha, hb]
  one_mem' := map_one α
  inv_mem' := by
    intro a ha
    change α a = a at ha
    change α a⁻¹ = a⁻¹
    rw [map_inv, ha]

@[simp] theorem mem_fixSub {T : Type*} [Group T] {α : MulAut T} {g : T} :
    g ∈ fixSub α ↔ α g = g := Iff.rfl

abbrev Z4pow (n : ℕ) : Type := Multiplicative (Fin n → ZMod 4)

abbrev Z4Z4Z2Z2 : Type := Multiplicative (ZMod 4 × ZMod 4 × ZMod 2 × ZMod 2)

structure Sigma3Rel {G : Type*} [Group G] (ρ x : G) : Prop where
  ord_ρ : orderOf ρ = 3
  ord_x : orderOf x = 2
  conj : x * ρ * x⁻¹ = ρ⁻¹

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
