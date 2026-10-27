module

public import CFSG.ClassicalInvolution.Uniform.U4Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4

variable {F : Type} [Group F] [Finite F]

theorem Mem3.comm_of_mem_normalizer {Y : Subgroup F} {y x : F} (hY : Mem3 Y y)
    (hx : x ∈ Subgroup.normalizer (Y : Set F)) : x * y = y * x := by
  have h1 : x * y * x⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hx y).mp hY.mem
  have h2 : (x * y * x⁻¹) * (x * y * x⁻¹) = 1 := by
    calc (x * y * x⁻¹) * (x * y * x⁻¹) = x * (y * y) * x⁻¹ := by group
      _ = 1 := by rw [hY.mul_self]; group
  rcases hY.isUniqueInvolution.unique _ h1 h2 with h3 | h3
  · exfalso
    apply hY.ne_one
    have : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [this, h3]
    group
  · exact mul_inv_eq_iff_eq_mul.mp h3

end CFSG.ClassicalInvolution.Q3.Q3T6B
