module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3Kit
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.EvenSporadicStandard.RuStd.S2

@[expose] def ruThreeClassCheck (_ : Unit := ()) : Bool :=
  gfr3ClassOK 4060 ruThreeC0Cert.pts 2160 4 1

end CFSG.HardMathSupport.Solomon.Coordinator
