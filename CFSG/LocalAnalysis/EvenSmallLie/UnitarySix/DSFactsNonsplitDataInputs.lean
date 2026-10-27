module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.CoverActionData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData
public meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.CoverActionData
public meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData
public meta import CFSG.LieType.Multipliers.U62Bridge
public meta import CFSG.LieType.Multipliers.U62Kernel
public meta import Certificates.Data.CFSGNative.F4.T46Simple
public meta import Certificates.Data.CFSGNative.Fi22.Local
public import Certificates.Certificate3180

public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62 CFSG.CosetTable CFSG.F4.Native
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Fischer CFSG.Sporadic.Fi22.Native

@[expose] def nsE : List (Fin 5 × Bool) :=
  [(0, true), (1, true), (1, true), (3, true), (2, true), (3, true), (1, true), (0, true),
    (1, false), (3, false), (2, false), (3, false), (1, false), (1, false), (4, true)]

@[expose] def nsN₁ : List (Fin 5 × Bool) :=
  [(1, true), (3, false), (2, false), (1, true), (0, false), (1, true), (1, true), (3, false),
    (0, true), (1, true), (3, true), (4, true), (3, true), (1, true), (3, true)]

@[expose] def nsN₂ : List (Fin 5 × Bool) :=
  [(3, false), (1, false), (1, false), (0, false), (1, false), (3, false), (1, true), (3, false),
    (1, true), (4, true), (3, true), (1, false), (3, true), (1, false), (2, false)]

@[expose] def nsC₁ : List (Fin 5 × Bool) := commWord nsN₁ nsE

@[expose] def nsC₂ : List (Fin 5 × Bool) := commWord nsN₂ nsE

end CFSG.EvenSmallLie.UnitarySix
