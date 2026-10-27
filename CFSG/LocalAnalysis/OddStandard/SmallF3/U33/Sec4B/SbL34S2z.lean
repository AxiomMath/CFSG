module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2s
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2c3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2d2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2e

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

theorem l34_s2 : L34S2Stmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau _ _ hl
  have hc := hl.toCtx4Q
  have hs := L34Z.isSylSL34_of_Ctx4L hl
  exact
    { toCtx4L := hl
      CG_O := L34Z.CG_O_eq hc hs
      CL_Obar := L34Z.CL_Obar_holds hc hs
      card_CQ_tau := L34Z.card_CQ_tau hc
      card_CQ_ttau := L34Z.card_CQ_ttau hc
      CQ_t_tau := L34Z.CQ_t_tau hc
      CQ_tau_type := L34Z.CQ_tau_type_holds hc
      CQ_ttau_type := L34Z.CQ_ttau_type_holds hc
      CO_base := L34Z.CO_base_holds hc hs }

end CFSG.OddStandard.SmallF3.HarrisU33
