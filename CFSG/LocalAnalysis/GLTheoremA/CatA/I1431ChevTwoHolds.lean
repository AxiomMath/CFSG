module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoAsm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoInn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoNC

public section

namespace CFSG.LocalAnalysis.GLTheoremA

section ChevTwo

theorem i1431ChevTwoS_holds : I1431ChevTwoS :=
  I1431C2.i1431ChevTwoS_of_residuals I1431C2.u42InnField_holds I1431C2.u42Outer_holds
    (I1431C2.u42FieldTwo_of_parts I1431C2.u42FieldTwoAt_classical
      I1431C2.u42FieldTwoAt_nonClassical)

end ChevTwo

end CFSG.LocalAnalysis.GLTheoremA

end
