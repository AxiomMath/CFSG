module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open scoped commutatorElement

variable {P : Type*} [Group P]

theorem extraspecial_two_commutatorElement_mem_center (hP : IsExtraspecialPGroup 2 P)
    (a b : P) : ⁅a, b⁆ ∈ center P := by
  rw [← hP.2.1, _root_.commutator_def]
  exact commutator_mem_commutator (mem_top a) (mem_top b)

theorem extraspecial_two_sq_mem_center [Finite P] (hP : IsExtraspecialPGroup 2 P) (x : P) :
    x ^ 2 ∈ center P := by
  rw [← hP.2.2.1, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  exact (CFSG.GroupTheory.frattini_elementary_quotient (p := 2) hP.1).2.2.1 _

end CFSG.LocalAnalysis.GorensteinLyons
