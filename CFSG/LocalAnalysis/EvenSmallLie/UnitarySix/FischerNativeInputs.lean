
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataBase
public import Certificates.Data.CFSGNative.Fischer.Polar

public section

namespace CFSG.EvenSmallLie.UnitarySix.Fischer

open CFSG.Fischer CFSG.Fischer.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Certificates

@[expose] def swapOK : Bool :=
  let T := tvTabs
  (List.range 693).all fun p => (List.range 693).all fun q =>
    ap T[p]! q == q || ap T[p]! q == ap T[q]! p

@[expose] def fixOK : Bool :=
  let T := tvTabs
  (List.range 693).all fun m => fixA.contains m ||
    fixA.any fun q => !(fixA.contains (ap T[m]! q))

end CFSG.EvenSmallLie.UnitarySix.Fischer
