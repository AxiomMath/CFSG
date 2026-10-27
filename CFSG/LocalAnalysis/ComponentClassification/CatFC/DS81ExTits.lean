module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTransport

public section

namespace CFSG.ComponentClassification.CatFC.DS81.Ex

open Subgroup CFSG.Open CFSG.Blueprint

set_option linter.unusedSectionVars false


theorem lie23To89At_Tits : Lie23To89At .Tits := by
  intro X _ _ n f hadm hM τ hτ h23
  have hn : n = 0 := hadm.2.2.1
  subst hn
  exact absurd (dvd_trans h23 (Subgroup.card_subgroup_dvd_card _))
    (not_twentythree_dvd_card_of_tits hadm hM)

theorem lie23To89At_twistedG2 : Lie23To89At .twistedG2 := by
  intro X _ _ n f hadm hM τ hτ h23
  exact absurd hadm.2.2.2.1 (by norm_num)

end CFSG.ComponentClassification.CatFC.DS81.Ex
