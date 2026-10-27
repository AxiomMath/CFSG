module

public import Certificates.Data.CFSGNative.Fi23.Data
public import Certificates.Data.CFSGNative.Th.Core

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.FrameJ

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native

set_option compiler.extract_closed false

@[expose] def fjPts : List Nat :=
  [0, 830, 1493, 1795, 10795, 4391, 13637, 29382, 17196, 14554, 8136, 4576, 21555, 13389, 6282,
    22056, 29944, 29779, 17072, 15480, 28185, 18757, 14065]

end CFSG.EvenSporadicStandard.TwoFi22.FrameJ
