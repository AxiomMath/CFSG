module

public import Certificates.Data.CFSGNative.Timmesfeld.Co1Seven

@[expose] public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.TwoBNative Timmesfeld.Co1Seven

@[expose] def rowsOrderFour (m : Rows) : Bool :=
  validRows m && pow m 4 == one () && pow m 2 != one ()

@[expose] def co1SevenOrderFourOK (aR bR : Rows) : Bool :=
  let rs := (gDag aR bR).1
  rowsOrderFour (mul (pow (rowAt rs 68) 3) (rowAt rs 69)) && rowsOrderFour (pow (rowAt rs 70) 7)

end CFSG.HardMathSupport.Dickson.I271
