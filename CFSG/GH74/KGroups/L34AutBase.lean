
module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.L34Base
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.L34Base
public import CFSG.GH74.KGroups.L34AutInputs
public meta import CFSG.GH74.KGroups.L34AutInputs
public import CFSG.GH74.KGroups.PSLN
public import CFSG.GH74.KGroups.FieldGF
public import CFSG.GH74.KGroups.L34Inputs

@[expose] public section

namespace CFSG.GH74.KGroups.L34

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix

theorem ws_pos : ∀ wk ∈ ws, 0 < wk.2 := by
  intro wk hwk
  simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hwk
  rcases hwk with rfl | rfl <;> norm_num

section Consequences

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

theorem finite_K : Finite K := Finite.of_equiv QP.originalSubgroup e.symm.toEquiv

end Consequences

end CFSG.GH74.KGroups.L34
