module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRu

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.RuSchreier
open CFSG.ComponentClassification.OuterAutomorphisms

theorem sporadicCase_Ru : SporadicCase .Ru := by
  refine sporadicCase_of_comps (fun G _ _ ⟨e⟩ t ht => ?_)
    (outer_of_forall_inner (mem_inner_of_mulEquiv ruEquivP mulAut_inner))
  exact (compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd ru_centralizerIn_comps
    (e.trans ruEquivP) t ht).mono fun Y _ h => not_small_of_not_three h

end CFSG.ComponentClassification.RestrictedStd.Spor
