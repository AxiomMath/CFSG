module

public import CFSG.ClassicalInvolution.Asc77.ModOApi

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

section Plain

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_oddCoreOf_of_mem_tri {Y : Subgroup G} {y o : G} (hy : y ∈ Y)
    (ho : o ∈ oddCoreOf Y) : y * o * y⁻¹ ∈ oddCoreOf Y := by
  obtain ⟨hoY, hoN⟩ := mem_oddCoreOf_iff.mp ho
  refine mem_oddCoreOf_iff.mpr ⟨Y.mul_mem (Y.mul_mem hy hoY) (Y.inv_mem hy), ?_⟩
  exact (classicalInvolutionOddCore_normal ↥Y).conj_mem _ hoN ⟨y, hy⟩

end Plain

end CFSG.ClassicalInvolution.Q3.Q3AM
