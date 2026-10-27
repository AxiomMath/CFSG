module

public import Certificates.Data.CFSGNative.GammaU.Pairs

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

@[expose] def resConjCheck (_ : Unit := ()) : Bool :=
  [0, 1].all fun i =>
    CFSG.GammaU.Native.nlOKAt (CFSG.GammaU.Native.spanList CFSG.GammaU.Native.d0)
      (CFSG.GammaU.Native.compOf i)
      ((CFSG.GammaU.Native.resConj i).map fun c => (c, CFSG.GammaU.Native.invR c))

end CFSG.GF2Type.Smith1979.GammaU.StepA
