module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4R
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFSpD
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFL4Sym
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFU4Bur
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Cases
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Kill
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphSymm

public section

namespace CFSG.ClassicalInvolution.Q3.TL4


theorem omegaAutOddFreeR_of_d4 (hD4 : D4OuterAutOddFreeR) : OmegaAutOddFreeR :=
  omegaAutOddFreeR_of SpL.outerFixedOddFree_psp L4.outerFixedOddFree_psl4
    U4.outerFixedOddFree_psu4 hD4

end CFSG.ClassicalInvolution.Q3.TL4
