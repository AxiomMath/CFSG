
module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.C9NativeInputsBase

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeClassesBase
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeModelBase1
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Sylow
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeModel
public meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataInputs

public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Fischer

@[expose] def c3 : Equiv.Perm (Fin 693) := evalCodes aGens [3]

@[expose] def sumCheck : Bool :=
  (fixedList 693 (arrOf c3)).length == 181 && (fixedList 693 (arrOf (j3 * c3))).length == 21

end CFSG.EvenSmallLie.UnitarySix
