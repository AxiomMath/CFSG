module

public import CFSG.LargeExtraspecial.AS35HSixEleven
public import CFSG.LargeExtraspecial.AS35MSixEightC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

namespace S14

theorem aschbacherSixElevenStmt_of_inputs'
    (hcore : AschbacherSixElevenFusionCoreStmt)
    (h592 : AschbacherFiveNineTwoStmt) (hT : SixFiveTransvectionStmt)
    (h67 : AschbacherSixSevenMbarStmt) (h59 : AschbacherFiveNineOneStmt)
    (hU : AschTwoAutStmt) : AschbacherSixElevenStmt :=
  aschbacherSixElevenStmt_of_fusion (aschbacherSixElevenFusionStmt_of_core hcore)
    (aschbacherSixEightOneStmt_of' hT h67 h59 hU) h592

end S14

end CFSG.LargeExtraspecial
