module

public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.SmallLocal

open Subgroup

variable {G : Type*} [Group G]

theorem mem_conjugate_iff {R : Subgroup G} {g x : G} :
    x ∈ conjugate R g ↔ g * x * g⁻¹ ∈ R := by
  simpa [conjugate, MulAut.conj_symm_apply] using
    (mem_map_equiv (f := MulAut.conj g⁻¹) (K := R) (x := x))

end CFSG.ComponentClassification.SmallLocal
