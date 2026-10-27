module

public import CFSG.Sporadic.Schreier.Outer
public import Certificates.Data.CFSGNative.SporadicSchreier.Count

public section

namespace CFSG.QuasithinUnique.Id2519.MathNoLayer
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

@[expose] def toTabs (l : List (List Nat)) : List Table :=
  l.map fun r => (r.map UInt32.ofNat).toArray

end CFSG.QuasithinUnique.Id2519.MathNoLayer
