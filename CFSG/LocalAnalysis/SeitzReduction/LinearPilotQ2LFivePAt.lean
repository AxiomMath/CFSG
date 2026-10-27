module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFivePMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveFldData

public section

namespace CFSG.SeitzReduction.LinearPilot

theorem lFiveSOneSylowPartAtInput : LFiveSOneSylowPartAtInput := by
  intro G _ _ L _ K _ _ hK e t ht hKt a b c d d' hab hdd' hca hcb hS X₀ hX₀ hX₀c W₁ hW₁c hW₁2
    hW₁t htW₁ hLW hj
  exact sylowPartAt_five hK e ht hKt hab hdd' hca hcb hS hX₀ hX₀c hW₁c hW₁2 hW₁t htW₁ hLW hj

end CFSG.SeitzReduction.LinearPilot
