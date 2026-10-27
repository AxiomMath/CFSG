module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreRankDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem exc3core_rankChk_E8 : ∀ C : Finset (Option (Fin Tag.E8.rank)), (∃ y, y ∉ C) →
    exc3core_noIso .E8 exc3core_thE8 C →
      exc3core_rankTabE8 (kacCount .E8 exc3core_thE8 C) C.card := by
  decide +kernel

end CFSG.LocalAnalysis.GLTheoremA.I167

end
