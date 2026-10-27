module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.AutExtHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Holds
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Cover4AFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Gen2AFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Gen5AFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Wit20Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Wit4AFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Wit5EFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

section Cert


theorem compatOpen_holds : CompatOpen :=
  ⟨cover4A_holds, wit4a_holds, gen5a_holds, wit5e_holds, wit20_holds, gen2A_holds⟩

theorem segevSection4_holds : HNRecog.SegevSection4 :=
  segevSection4_of_open autExtOpen_holds compatOpen_holds

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section4
