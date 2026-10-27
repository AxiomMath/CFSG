module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13M
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbStmt2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13k
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13p

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

theorem ctx13b_of_a (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    Ctx13B t L S x₁ x₂ lam rho tau om :=
  { toCtx13A := hc, Q_comm := S4B.c13_Q_comm hc, sq_V := S4B.c13_sq_V hc,
    Y_elem := S4B.c13_Y_elem hc, V_le_Y := S4B.c13_V_le_Y hc,
    normal_Y := S4B.c13_normal_Y hc, fpf_YV := S4B.c13_fpf_YV hc,
    fpf_QY := S4B.c13_fpf_QY hc }

theorem ctx13m_of_d (hc : Ctx13D t L S x₁ x₂ lam rho tau om) :
    Ctx13M t L S x₁ x₂ lam rho tau om :=
  { toCtx13D := hc, phi_Q' := S4B.c13_phi_Q hc.toCtx13A,
    data_V := S4B.c13_data_V hc.toCtx13C, tG_Qom := S4B.c13_tG_Qom hc.toCtx13C,
    cent_M_Y := S4B.c13_cent_M_Y hc.toCtx13C, comm_Y := S4B.c13_comm_Y hc.toCtx13C,
    cent_R := S4B.c13_cent_R hc.toCtx13C, K_le := S4B.c13_K_le hc.toCtx13C,
    M_le_K := S4B.c13_M_le_K hc.toCtx11, U_le_K := S4B.c13_U_le_K hc.toCtx11,
    normal_Q_K := S4B.c13_normal_Q_K hc.toCtx13C }

theorem ctx13_of_m (hc : Ctx13M t L S x₁ x₂ lam rho tau om)
    (hK : Ctx13KFacts t x₁ x₂ lam rho tau om) : Ctx13 t L S x₁ x₂ lam rho tau om :=
  { toCtx11 := hc.toCtx11, q_iso := hc.q_iso, om_sq := by simpa [pow_two] using hc.om_sq,
    om_not_mem := hc.om_not_mem, CO_eq := hc.CO_eq, t_om := hc.t_om, lam_om := hc.lam_om,
    O_cent := hc.O_cent, phi_Q' := hc.phi_Q', data_V := hc.data_V, normal_Y := hc.normal_Y,
    Y_cent := hc.Y_cent, Y_comm := hc.Y_comm, tau_cent_Y := hc.tau_cent_Y,
    tau_inv_Q := hc.tau_inv_Q, om_cent_Y := hc.om_cent_Y, tG_Qom := hc.tG_Qom,
    cent_M_Y := hc.cent_M_Y, Q_om := hc.Q_om, Q_omtau := hc.Q_omtau, comm_Y := hc.comm_Y,
    cent_R := hc.cent_R, K_le := hc.K_le, M_le_K := hc.M_le_K, tK := hK.2.1,
    U_le_K := hc.U_le_K, card_K := hK.1, K_eq := hK.2.2.1, normal_Q_K := hc.normal_Q_K,
    CK_rho := hK.2.2.2 }

theorem ctx13_exists_of_K (hK : Ctx13KStmt) : Ctx13ExistsStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau hG hc h12 h13
  obtain ⟨om, hA⟩ := S4B.ctx13a_exists hc h13
  have hM : Ctx13M t L S x₁ x₂ lam rho tau om :=
    ctx13m_of_d (S4B.ctx13d_of_c (S4B.ctx13c_of_b (ctx13b_of_a hA)))
  exact ⟨om, ctx13_of_m hM (hK hG hM)⟩

end CFSG.OddStandard.SmallF3.HarrisU33
