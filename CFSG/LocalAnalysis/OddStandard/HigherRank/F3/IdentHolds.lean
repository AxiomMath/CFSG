module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.IdentMain
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpHolds
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG CFSG.ComponentClassification

theorem identGenInput_holds
    : IdentGenInput :=
  identGenInput_of GS82PumpInputs.chevOddCentralPumpInput_holds
    GS82PumpInputs.spFourThreeCentralPumpInput_holds TBLit.griessMultipliersAllModels_holds
    (fun _ _ h => CFSG.LieType.Steinberg.CentralExt.GriessNative.e7_row (p := 3) (f := 1)
      (h.chevalleyExceptionalModel (by decide)))
    CatLeafProof.lieOrderFormulasInput

end CFSG.OddStandard.HigherRank.F3
