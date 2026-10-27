module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4ResRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4ResInv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4ResPGL
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09TD4G2A

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDescTD4

set_option linter.unusedSectionVars false


theorem td4Res_holds : HDesc.TD4Res := fun q hv hq2 _ hchev =>
  goodSubAt_triD4 triD4InvCentRankOne_holds pglThreeInvGood_holds q hv
    (td4g2_p_two hv (MulEquiv.refl _) hchev) hq2

end CFSG.LocalAnalysis.GLTheoremA.HDescTD4
