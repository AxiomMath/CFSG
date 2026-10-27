module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapBE

public section

namespace CFSG.ComponentClassification.SolMax

namespace SwapP2

theorem signalizerSwapMemberNarrowInput_of_residue (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hres : SwapMemberResidue) :
    SignalizerSwapMemberNarrowInput :=
  signalizerSwapMemberNarrowInput_of_inputs h33 h35 hPump hN1 (pumpSide_of_inputs hPump hN1)
    (pumpDiag_of_inputs h33 h35 hPump hN1) hres

end SwapP2

end CFSG.ComponentClassification.SolMax
