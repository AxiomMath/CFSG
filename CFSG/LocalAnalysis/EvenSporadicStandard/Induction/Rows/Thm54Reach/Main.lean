module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.CaseA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.Index
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Reduce
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.EvenSporadicStandard.Induction.Thm54Reach

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Induction

theorem sol78Thm54ReachIndex_two (I : CatInputs) : Sol78Thm54ReachIndex 2 := by
  intro Y _ _ N' hN hidx hkp P hP hq hT h29
  exact reach_of_catalog I hN hidx.le (Balance.catalog_of_index_two hN hidx hkp) hP hq hT h29

end CFSG.EvenSporadicStandard.Induction.Thm54Reach
