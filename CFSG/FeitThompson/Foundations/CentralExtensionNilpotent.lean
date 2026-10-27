module
public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Foundations.NilpotentHomImageNilpotent

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem normal_of_le_center {N : Subgroup G} (hN : N ≤ Subgroup.center G) : N.Normal where
  conj_mem n hn g := by
    have hcomm := Subgroup.mem_center_iff.mp (hN hn) g
    simpa [hcomm] using hn

theorem isNilpotent_of_isNilpotent_quotient_of_le_center {N : Subgroup G} [N.Normal]
    (hN : N ≤ Subgroup.center G) [Group.IsNilpotent (G ⧸ N)] : Group.IsNilpotent G :=
  Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' N) (by rwa [QuotientGroup.ker_mk'])

end CFSG.FeitThompson
