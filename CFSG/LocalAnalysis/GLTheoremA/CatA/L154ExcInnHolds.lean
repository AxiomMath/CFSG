module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154RealA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154RealE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcRestAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

section Holds

theorem l154LangInnRes_holds : L154LangInnRes :=
  l154LangInnRes_of_real l154RealTypeA_holds l154RealE6_holds l154NonCfgOutdiag_holds

theorem l154OmegaNID_excUntw_holds : L154OmegaNID l154ExcUntw :=
  l154OmegaNID_excUntw l154LangInnRes_holds

theorem l154OmegaNID_excTwE6_holds : L154OmegaNID l154ExcTwE6 :=
  l154OmegaNID_excTwE6 l154LangInnRes_holds

theorem l154OmegaNID_excTriD4_holds : L154OmegaNID l154ExcTriD4 :=
  l154OmegaNID_excTriD4 l154LangInnRes_holds

theorem l154NIDOn_excRest_of_ree (hRee : L154NIDOn l154ExcRee) : L154NIDOn l154ExcRest :=
  l154NIDOn_excRest l154LangInnRes_holds hRee

end Holds

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
