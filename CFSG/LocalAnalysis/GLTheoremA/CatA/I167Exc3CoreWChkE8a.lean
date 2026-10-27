module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

theorem exc3core_wCheck_E8_0 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop (1641 * 0)).take 1641) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_1 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop (1641 * 1)).take 1641) = true := by
  decide +kernel


end CFSG.LocalAnalysis.GLTheoremA.I167

end
