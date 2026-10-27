module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def IP_P_closed (x : G) (T P : Subgroup G) : Prop :=
  ∀ c ∈ Subgroup.centralizer ({x} : Set G), ∀ v ∈ P, c * v * c⁻¹ ∈ T → c * v * c⁻¹ ∈ P

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
