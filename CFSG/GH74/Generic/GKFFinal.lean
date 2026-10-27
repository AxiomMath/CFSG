module

public import CFSG.GH74.Generic.GKFMain
public import CFSG.Adapters.TauCetiExceptional.ReeCatalog

public section

namespace CFSG.GH74.Generic

open CFSG.ComponentClassification.TBLit in
theorem genericKnownFacts_of_griess
    (hGA : GriessMultipliersAllModels) : GenericKnownFacts :=
  genericKnownFacts_of_griess_bridges hGA CFSG.TauCetiBridge.typewiseBridges

end CFSG.GH74.Generic
