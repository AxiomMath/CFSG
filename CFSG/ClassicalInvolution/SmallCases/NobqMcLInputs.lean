module

public import CFSG.Assembly.Defs
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLCheckInputs

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ClassicalInvolution.McLData CFSG.ClassicalInvolution.McLProof

@[expose] def noncentralInvOK : Bool :=
  (mulClosureH 275 sgens.toArray capK).1.any fun T => involOK 275 T && !tblEq 275 T Ta

end CFSG.ClassicalInvolution.Nobq
