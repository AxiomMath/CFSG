module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81Alt
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81Spor
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81LieDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Lemma210Two

public section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic

set_option linter.unusedSectionVars false


theorem ds81_of_lie (ho : DS81OddLie) (he : DS81EvenLie) :
    CFSG.EvenSporadicStandard.TwoB.DS81Lemma210Two := by
  intro X _ _ _ hna hcat τ hτ hchar hab
  rcases (CFSG.Milestones.ct_catalog_nonabelian_type_partition X hna).1 hcat with
    ⟨n, hn, ⟨θ⟩⟩ | hodd | heven | ⟨s, ⟨e⟩⟩
  · exact ds81_alternating hn θ τ hτ hchar hab
  · exact ho X hna hodd τ hτ hchar hab
  · exact he X hna heven τ hτ hchar hab
  · exact ds81_sporadic hna e τ hτ hchar hab

end CFSG.ComponentClassification.CatFC.DS81
