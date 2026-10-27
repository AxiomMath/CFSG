module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBTransferB
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abMain

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8abB

theorem caseB : KD8ab.CaseB := by
  intro _ X _ _ _ hX _ t L A C S T₁ G hq₁ hq₂
  obtain ⟨D⟩ := BData.nonempty_t2Data (⟨G, hq₁, hq₂⟩ : BData S T₁)
  exact D.false_of_transfer hX

end KD8abB

end CFSG.ComponentClassification.HSFLit
