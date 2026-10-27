module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3U43
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Chain

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TS8J

open CFSG.EvenSporadicStandard.M24Std.CU43

theorem P_le_U43Ext :
    CFSG.EvenSporadicStandard.M24Std.CU43.P ≤ U43Ext := by
  rw [P_eq_range]
  rintro _ ⟨x, rfl⟩
  exact Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)

end CFSG.EvenSporadicStandard.Fin76b.TS8J
