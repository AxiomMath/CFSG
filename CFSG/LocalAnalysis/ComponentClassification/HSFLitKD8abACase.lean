module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAJ
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abMain

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG

namespace KD8ab

theorem caseA : CaseA := by
  intro _ X _ _ _ hX _ t L A C S T₁ G h₁ h₂
  obtain ⟨T⟩ := AD.nonempty_TD ⟨G, h₁, h₂⟩
  cases he : T.e
  · exact T.false_of_e_false hX he
  · exact T.false_of_e_true hX he

end KD8ab

end CFSG.ComponentClassification.HSFLit
