module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4HbarCases
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Main

public section

namespace CFSG.OddStandard.AltStdSmall4.HbarCoords

theorem sec4HbarCases_holds : Sec4HbarCases :=
  sec4HbarCases_of GL62.gl62Overgroups_holds

theorem sec4HbarIdent_holds : Sec4HbarIdent :=
  sec4HbarIdent_of GL62.gl62OvergroupsEq_holds

end CFSG.OddStandard.AltStdSmall4.HbarCoords
