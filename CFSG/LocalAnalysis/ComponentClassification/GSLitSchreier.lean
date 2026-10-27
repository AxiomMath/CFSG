module

public import CFSG.LocalAnalysis.ComponentClassification.UGSChainRankTwoMaximality
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs

public section

namespace CFSG.ComponentClassification.GSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem globallyFirstRankTwoInput_of_schreier (hS : SchreierFor Blueprint.Catalog) :
    GloballyFirstRankTwoInput :=
  fun _ _ _ hK hZ _ _ _ hU hJ2 hfirst hrank hsyl =>
    UGSChain.globally_first_maximal_rank_two_unbalancing_maximality_of_schreier hS hK hZ hU hJ2
      hfirst hrank hsyl

end CFSG.ComponentClassification.GSLit
