module

public import CFSG.GH74.Generic.S1.KL3Final
public import CFSG.GH74.Generic.S1.KL3ClSurv

public section

namespace CFSG.GH74.Generic.S1

theorem kl3Table_of_griess (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    KL3Table :=
  kl3Table_of_survL4 hGA (kl3SurvL4 hGA)

end CFSG.GH74.Generic.S1
