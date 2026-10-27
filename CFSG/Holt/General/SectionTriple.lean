module

public import CFSG.Holt.General.Defs
import CFSG.Assembly.Defs

public section

namespace CFSG.Holt.General

open Subgroup MulAction
open scoped Pointwise

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] {z : G} {α : Ω}

@[expose] def sectionGroup (B : Subgroup G) (z : G) : Subgroup G :=
  B ⊔ zpowers z

abbrev sectionSet (B : Subgroup G) (z : G) (α : Ω) : Set Ω :=
  orbit (sectionGroup B z) α

@[expose] def sectionInvolution (B : Subgroup G) (z : G) : sectionGroup B z :=
  ⟨z, mem_sup_right (mem_zpowers z)⟩

@[expose] def sectionPoint (B : Subgroup G) (z : G) (α : Ω) : sectionSet B z α :=
  ⟨α, mem_orbit_self α⟩

@[simp]
theorem coe_sectionInvolution (B : Subgroup G) (z : G) : (sectionInvolution B z : G) = z :=
  rfl

@[simp]
theorem coe_sectionPoint (B : Subgroup G) (z : G) (α : Ω) : (sectionPoint B z α : Ω) = α :=
  rfl

end CFSG.Holt.General
