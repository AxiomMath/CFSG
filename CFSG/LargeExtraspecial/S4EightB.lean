module

public import CFSG.LargeExtraspecial.OrthoF2Basic
public import CFSG.LargeExtraspecial.S4EightG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem isotropic_span {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {β : LinearMap.BilinForm (ZMod 2) V} {P : Set V} (hP : ∀ x ∈ P, ∀ y ∈ P, β x y = 0) :
    ∀ u ∈ Submodule.span (ZMod 2) P, ∀ w ∈ Submodule.span (ZMod 2) P, β u w = 0 := by
  have h1 : ∀ x ∈ P, ∀ w ∈ Submodule.span (ZMod 2) P, β x w = 0 := by
    intro x hx w hw
    induction hw using Submodule.span_induction with
    | mem y hy => exact hP x hx y hy
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul r y _ hy => rw [map_smul, hy, smul_zero]
  intro u hu w hw
  induction hu using Submodule.span_induction with
  | mem x hx => exact h1 x hx w hw
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add y z _ _ hy hz => rw [map_add, LinearMap.add_apply, hy, hz, add_zero]
  | smul r y _ hy => rw [map_smul, LinearMap.smul_apply, hy, smul_zero]

end CFSG.LargeExtraspecial.S4
