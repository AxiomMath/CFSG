module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Stmt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0e
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0g2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0h
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0i

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

theorem l34_s0 : L34S0Stmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau hG _ hc _ hs
  exact
    { toCtx4Q := hc
      Q_inf := L34Z.Q_inf_T hc
      Z_Q := L34Z.Z_Q hc hs
      Z_O := L34Z.Z_O_eq hc hs
      O_comm := L34Z.O_comm_eq hc
      comm_t := L34Z.comm_t_eq hc
      comm_tau := L34Z.comm_tau_eq hc
      comm_ttau := L34Z.comm_ttau_eq hc
      normal_base_U := L34Z.normal_base_U hc
      tauU := L34Z.tauU_eq hc
      ttauU := L34Z.ttauU_eq hc
      char_V := L34Z.char_V hc hs
      char_O := L34Z.char_O hc hs
      U_not_sylow := L34Z.U_not_sylow_top hc hG
      normal_CQtau := L34Z.normal_CQtau hc
      normal_CQttau := L34Z.normal_CQttau hc
      card_CQ_tl := L34Z.card_CQ_tl hc hs
      CU_tl := L34Z.CU_tl hc
      card_CU_tl := L34Z.card_CU_tl hc hs
      tG_N := L34Z.tG_N_field hc
      tG_tN := L34Z.tG_tN_field hc
      inv_tl := L34Z.inv_tl_field hc
      inv_l := L34Z.inv_l_field hc
      inv_tltau := L34Z.inv_tltau_field hc
      inv_ltau := L34Z.inv_ltau_field hc }

end CFSG.OddStandard.SmallF3.HarrisU33
