module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d8e
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dI4b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d2c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

theorem q13d_famD : Q13FamD := by
  intro G _ _ t L S x₁ x₂ lam rho tau om hq hA hB hC
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
  rcases hA.A_dich with hI | hII
  · exact (q13d_caseI_false h hB hC hI).elim
  · exact
      { A_cent := hII
        gam_sq := q13d_gam_sq h
        P_iso := q13d_P_iso h hII
        t_inv_P := q13d_t_inv_P h hII
        E0_eq := q13d_E0_eq h
        P_char := ⟨q13d_P_char_E0 h hII, q13d_E0_char_U h hB⟩
        CP_rho := q13d_CP_rho h hII
        comm_P_rho := q13d_comm_P_rho h hII
        rho_norm := q13d_rho_norm h
        M_le_L := q13d_M_le_L h hB
        cent_E0 := q13d_cent_E0 h
        tL := q13d_tL h hII
        CL_t := q13d_CL_t h hB
        rho_syl3 := q13d_rho_syl3 h hB hII
        L_card := q13d_L_card h hB hII
        B_two := q13d_B_two h hII
        B_normal := q13d_B_normal h
        E0_le_B := q13d_E0_le_B h
        L_eq := q13d_L_eq h hB hII }

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
