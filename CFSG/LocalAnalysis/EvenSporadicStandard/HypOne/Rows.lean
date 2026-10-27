module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rank
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernel

public section

namespace CFSG.EvenSporadicStandard.HypOne

open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 CFSG.EvenSmallLie

structure FullRowData (Y : Type*) [Group Y] [Finite Y] : Prop where
  rowData : Finkelstein77.RowData Y
  fours : FoursGroupCondition Y

theorem FullRowData.of_parts {Y : Type*} [Group Y] [Finite Y] (hI : HypothesisOne Y)
    (h8 : HasElemAbelianEight Y) (hF : FoursGroupCondition Y) : FullRowData Y :=
  ⟨rowData_of_hasElemAbelianEight hI h8, hF⟩

end CFSG.EvenSporadicStandard.HypOne
