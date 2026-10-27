module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixMDual

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

theorem lFiveSwapGOneInput_of_labelDualAt
    (hlab : LinearTwoSwapLabelDualAtInput 5) : LFiveSwapGOneInput := by
  intro G _ _ L hset K _ _ hK t ht hKt hhyp e hall
  exact exists_gOne_of_labelDual_of_dvd hlab hset (by norm_num) hK e ht hKt
    (two_pow_le_of_dvd_factorial_five hK) hhyp hall

end CFSG.SeitzReduction.LinearPilot
