module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3Lie
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3Spor
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerE1Weak

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic


theorem kgHS3_holds : CFSG.EvenSporadicStandard.HSStd.Zassenhaus.KGHS3 := by
  intro S _ _ hCat hSimple h3 K hKq hKHS
  have hK : HSType ↥K := ⟨hKq, hKHS⟩
  rcases hCat with ⟨p, _, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hCl | hEx | hSpor
  · exact (kgHS3_cyclic e K hKq).elim
  · exact (kgHS3_alt hn e h3 K hK).elim
  · exact (false_of_lie_model hSimple h3 K hK (Or.inl hCl)).elim
  · exact (false_of_lie_model hSimple h3 K hK (Or.inr hEx)).elim
  · exact kgHS3_sporadic hSpor h3 K hK

end CFSG.ComponentClassification.CatFC.KGHS3
