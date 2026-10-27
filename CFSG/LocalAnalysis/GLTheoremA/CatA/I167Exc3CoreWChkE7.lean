module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

theorem exc3core_wCheck_E7 :
    exc3core_wCheck .E7 127 exc3core_uniE7 exc3core_dngE7 (RD.allVecs Tag.E7.rank) = true := by
  decide +kernel

theorem exc3core_eCheck_E7 : ∀ d ∈ RD.allVecs Tag.E7.rank,
    exc3core_eCheck .E7 127 exc3core_uniE7 exc3core_dngE7 d = true :=
  List.all_eq_true.1 exc3core_wCheck_E7

end CFSG.LocalAnalysis.GLTheoremA.I167

end
