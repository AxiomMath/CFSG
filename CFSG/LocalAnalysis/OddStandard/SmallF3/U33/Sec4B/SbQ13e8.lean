module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e7e

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

theorem q13e_famE : Q13FamE := by
  intro G _ _ t L S x₁ x₂ lam rho tau om hq hA hB hC hD
  have hom_mem : om ∈ ctxCO t tau x₁ x₂ rho := by
    rw [hA.CO_eq]
    exact Subgroup.subset_closure (by simp)
  have h : Q13Om t L S x₁ x₂ lam rho tau om :=
    { toQ13Ctx := hq
      om_mem := hom_mem
      om_sq := by rw [← pow_two]; exact hA.om_sq
      om_not_mem := hA.om_not_mem
      t_om := hA.t_om
      CO_eq := hA.CO_eq }
  exact q13e_false h hB hC hD

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
