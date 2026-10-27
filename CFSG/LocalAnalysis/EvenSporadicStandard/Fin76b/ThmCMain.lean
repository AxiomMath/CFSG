module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCJ2Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCJ3Data

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem fin76bThmCSimple_of_outerRest_models
    (hR : Fin76bOuterRest) : Fin76bThmCSimple :=
  fin76bThmCSimple_of_outerRest hR J2.outerData_P J3.outerData_j3P

end CFSG.EvenSporadicStandard.Fin76b
