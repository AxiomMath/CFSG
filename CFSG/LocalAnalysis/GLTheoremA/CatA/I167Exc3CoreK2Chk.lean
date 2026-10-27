module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreK2Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

theorem exc3core_k2Check_E7 :
    (RD.allVecs Tag.E7.rank).all (exc3core_k2Check .E7 127 exc3core_uD6) = true := by
  decide +kernel

theorem exc3core_k2Check_E7' : ∀ d ∈ RD.allVecs Tag.E7.rank,
    exc3core_k2Check .E7 127 exc3core_uD6 d = true :=
  List.all_eq_true.1 exc3core_k2Check_E7

end CFSG.LocalAnalysis.GLTheoremA.I167

end
