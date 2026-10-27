module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.EndMain
public import CFSG.LocalAnalysis.OddStandard.Harada75
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisE16e
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisCore
public import CFSG.Quasithin.Recognition.HSType17m

public section

namespace CFSG.OddStandard.SmallF3.L33

open CFSG.ComponentClassification

theorem smallF3L33Core_of
    (hGH74 : UFrontier.GH74ModelsInput) : SmallF3L33Core :=
  smallF3L33Core_of_inputs hGH74 OddStandard.Harada75.haradaInput_holds
    (GHarris.gorensteinHarrisInput_of GHarris.gorensteinHaradaThmCInput_holds
      CFSG.Quasithin.HSType.statementI48_holds)

end CFSG.OddStandard.SmallF3.L33
