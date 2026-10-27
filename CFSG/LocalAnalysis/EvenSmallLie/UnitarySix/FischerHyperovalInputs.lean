module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import Certificates.Data.CFSGNative.Fischer.Hyperoval

public section

namespace CFSG.EvenSmallLie.UnitarySix.Fischer

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

@[expose] def domOK (k : ℕ) : Bool :=
  let F := rootFlags k
  let T := tvTabs
  (List.range 693).all fun q => F[q]! ||
    (List.range 693).any fun x => F[x]! && ap T[q]! x == x

end CFSG.EvenSmallLie.UnitarySix.Fischer
