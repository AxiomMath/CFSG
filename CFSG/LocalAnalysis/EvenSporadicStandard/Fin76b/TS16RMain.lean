module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Holds
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16Loc

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem fin76bOuterS16Loc_of_kbar
    (hK : Fin76bS16KBar) (hH : Harada75E8) : Fin76bOuterS16Loc := by
  intro G _ _ L z t T E Q x B β h
  obtain ⟨S, c⟩ := h.exists_ctx
  exact c.loc (hK G L z t T E Q x B β h S c.S2 c.SC c.Smax c.zS c.card16) hH

theorem fin76bOuterS16Loc_of_kbarFacts
    (hK : Fin76bS16KBar) : Fin76bOuterS16Loc :=
  fin76bOuterS16Loc_of_kbar hK harada75E8_holds

end CFSG.EvenSporadicStandard.Fin76b
