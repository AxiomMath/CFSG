
module

public import CFSG.Fischer.Polar.Basic
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataBase
public meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataBase
public import CFSG.Fischer.HermitianEquiv
public import Certificates.Data.CFSGNative.Fischer.Xi22

public section

namespace CFSG.EvenSmallLie.UnitarySix.Hunt

open CFSG.Fischer CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native
open CFSG.Sporadic.Schreier

@[expose] def braidOK (T : Array Table) : Bool :=
  allIn 0 693 fun m => allIn 0 693 fun m' => ap T[m]! m' == m' || ap T[m]! m' == ap T[m']! m

end CFSG.EvenSmallLie.UnitarySix.Hunt
