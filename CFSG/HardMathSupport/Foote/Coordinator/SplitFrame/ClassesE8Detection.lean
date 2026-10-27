module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Classes
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detection
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Normalizer
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.NormalizerSmall

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration


theorem seitzExcAnisotropicE8Class_five_of_detection
    (hD : ∀ (K : Type) [Field K] [Finite K], FrameDetection .E8 K (cosetRoots .E8 4 5))
    (hN2 : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      FrameNormalizerSolvable .E8 K (cosetRoots .E8 4 5)) :
    SeitzExcAnisotropicE8Class 5 := by
  refine seitzExcAnisotropicE8Class_five_of_frame
    (fun K _ _ => frameClosing_of_detection_E8 K (hD K)) (fun K _ _ => ?_)
  have h2 : 1 < Nat.card K := Finite.one_lt_card
  rcases (show 4 ≤ Nat.card K ∨ Nat.card K = 3 ∨ Nat.card K = 2 by omega) with h4 | h3 | h2'
  · exact frameNormalizerSolvable_E8 K h4
  · exact frameNormalizerSolvable_E8_three K h3
  · exact hN2 K h2'

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
