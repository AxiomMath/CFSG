module

public import CFSG.LargeExtraspecial.Asc611Main
public import CFSG.LargeExtraspecial.Asc611Outer

public section

namespace CFSG.LargeExtraspecial

namespace S14

theorem aschbacherSixElevenFusionMStmt_of_inner
    (hI : UnitaryInnerCentStmt) :
    AschbacherSixElevenFusionMStmt :=
  aschbacherSixElevenFusionMStmt_of_unitaryCent
    (aschbacherUnitaryCentStmt_of hI unitaryOuterCentStmt)

end S14

end CFSG.LargeExtraspecial
