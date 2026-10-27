module

public import CFSG.Holt.General.Defs

public section

namespace CFSG.Holt.General

open MulAction Subgroup

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

@[simp]
theorem rangeRestrict_toPermHom_smul (g : G) (ω : Ω) :
    (toPermHom G Ω).rangeRestrict g • ω = g • ω :=
  rfl

variable {z : G} {α : Ω}

end CFSG.Holt.General
