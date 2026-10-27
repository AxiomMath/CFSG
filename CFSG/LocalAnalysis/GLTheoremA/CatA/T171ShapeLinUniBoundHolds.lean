module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniBlockHoldsMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLinStatedMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundNonCommLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundNonCommUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundA0
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Mark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9Frame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Size

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh


theorem linUniBoundOther_holds : LinUniBoundOther :=
  linUniBoundOther_of_block (linBlockInnDiag_of_stated linBlockInnDiagStated_holds)
    uniBlockInnDiag_holds linTypeOneNonComm_holds uniTypeOneNonComm_holds
    linFieldTypeA0Bound_holds uniFieldTypeA0Bound_holds

theorem linUniBound_holds : LinUniBound :=
  linUniBound_of_u6 u6Marking_holds u6Type9_holds u6SizeModel_holds linUniBoundOther_holds

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
