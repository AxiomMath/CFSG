module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporMathieu
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporJ2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporJ3
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporMcL
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG CFSG.Blueprint

theorem cf67J2_thm :
    CF67J2 :=
  cf67Fam_of_noN2 fun Y _ _ h => noN2_J2 Y h

theorem cf67J3_thm :
    CF67J3 :=
  cf67Fam_of_noN2 fun Y _ _ h => noN2_J3 Y h

theorem cf67McL_thm :
    CF67McL :=
  cf67Fam_of_noN2 fun Y _ _ h => noN2_McL Y h

theorem cf67Spor_thm :
    CF67Spor :=
  cf67Spor_of_parts cf67M11_thm cf67M12_thm cf67M22_thm cf67M23_thm cf67J2_thm cf67J3_thm

theorem cf67McLy_thm
    (hLy : CF67Ly) : CF67McLy :=
  cf67McLy_of_parts cf67McL_thm hLy

end CFSG.GH74.GLS.Stage2.Bender.Thm1
