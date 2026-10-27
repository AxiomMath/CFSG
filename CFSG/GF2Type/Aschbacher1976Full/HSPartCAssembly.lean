module

public import CFSG.GF2Type.Aschbacher1976Full.HSDischarge
public import CFSG.GF2Type.Aschbacher1976Full.HSPartC
public import CFSG.GF2Type.Aschbacher1976Full.HSFinite

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

theorem sixStmt_holds : SixStmt := fun ι hι hO2 a ha hP1 hK4 =>
  six_classify ι hι hO2 a ha hP1 hK4

theorem hsPartC_holds : HSPartC :=
  hsPartC_of_inputs embedStmt_holds autStmt_holds burnsideStmt_holds sixStmt_holds

end CFSG.GF2Type.Aschbacher1976Full.HS
