module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

theorem exc3core_wCheck_E6 :
    exc3core_wCheck .E6 73 exc3core_dngE6 exc3core_dngE6 (RD.allVecs Tag.E6.rank) = true := by
  decide +kernel

theorem exc3core_eCheck_E6 : ∀ d ∈ RD.allVecs Tag.E6.rank,
    exc3core_eCheck .E6 73 exc3core_dngE6 exc3core_dngE6 d = true :=
  List.all_eq_true.1 exc3core_wCheck_E6

end CFSG.LocalAnalysis.GLTheoremA.I167

end
