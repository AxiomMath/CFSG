module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreRankDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem exc3core_rankChk_F4 : ∀ C : Finset (Option (Fin Tag.F4.rank)), (∃ y, y ∉ C) →
    exc3core_noIso .F4 exc3core_thF4 C →
      exc3core_rankTabF4 (kacCount .F4 exc3core_thF4 C) C.card := by
  decide +kernel

theorem exc3core_rankChk_E6 : ∀ C : Finset (Option (Fin Tag.E6.rank)), (∃ y, y ∉ C) →
    exc3core_noIso .E6 exc3core_thE6 C →
      exc3core_rankTabE6 (kacCount .E6 exc3core_thE6 C) C.card := by
  decide +kernel

theorem exc3core_rankChk_E7 : ∀ C : Finset (Option (Fin Tag.E7.rank)), (∃ y, y ∉ C) →
    exc3core_noIso .E7 exc3core_thE7 C →
      exc3core_rankTabE7 (kacCount .E7 exc3core_thE7 C) C.card := by
  decide +kernel

end CFSG.LocalAnalysis.GLTheoremA.I167

end
