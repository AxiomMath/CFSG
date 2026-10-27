module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.CentGenCheck
public import Certificates.Data.CFSGNative.Fi24.Sep

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Sporadic.Fi24.Native

@[expose] def fi24Ops : NatOps (Array W) where
  one := idW 781
  mul := mulW
  pow := powW 781
  eqb := eqRows 781
  neb := fun X Y => !eqRows 781 X Y

end CFSG.HardMathSupport.Dickson.I271
