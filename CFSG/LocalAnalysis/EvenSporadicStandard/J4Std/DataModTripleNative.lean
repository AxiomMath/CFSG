module

public import CFSG.Sporadic.J4.QT2LocNative

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataMod

open CFSG.Sporadic.J4.QT2

@[expose] def chkTriple : Bool :=
  tMasks.all (fun c => decide (c < 2048)) && !tMasks.contains 23

end CFSG.EvenSporadicStandard.J4Std.DataMod
