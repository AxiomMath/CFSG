module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Theta
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Quot
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.MS1
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.MS2
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Short

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub

theorem e0SubConfigStatement_holds : E0SubConfigStatement :=
  e0SubConfigStatement_of_fine_pieces thetaSubLStmt_holds normSubLStmt_holds
    altQuotSubLStmt_holds notNormSubLStmt_holds sQTKSubLStmt_holds mS2SubLStmt_holds
    shortCommSubLStmt_holds normalClosureSubLStmt_holds

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub
