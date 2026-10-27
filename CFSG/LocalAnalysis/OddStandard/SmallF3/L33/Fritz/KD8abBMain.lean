module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBTransferB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abMain

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8abB

theorem caseB : KD8ab.CaseB := by
  intro _ X _ _ _ hX _ t L A C S T₁ G hq₁ hq₂
  obtain ⟨D⟩ := BData.nonempty_t2Data (⟨G, hq₁, hq₂⟩ : BData S T₁)
  exact D.false_of_transfer hX

end KD8abB

end CFSG.OddStandard.SmallF3.L33.KD
