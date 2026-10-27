module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModelBridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResModel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes

open CFSG.EvenSmallLie.OmegaEight CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModel

theorem modelFactD42_of_cert : ModelFactD42 := by
  intro Q _ _ hQ
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hQ
  exact autOddFree_of_fullOddCoreStmt (FullOddCore.of_mulEquiv e.symm fullOddCore_omegaT)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
