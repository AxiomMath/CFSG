module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7AbsMain
public import CFSG.Timmesfeld.Final.Simple

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

theorem s7_lieModelSimpleU43 : LieModelSimpleU43 :=
  fun N _ h => CFSG.Timmesfeld.isSimpleGroup_of_lieModel h

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
