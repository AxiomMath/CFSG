module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Classes
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.RootClosureF4Sound
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Normalizer
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.NormalizerSmallF4

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration


theorem seitzExcAnisotropicF4Class_three_of_detection
    (hD : ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K →
      FrameDetection .F4 K (cosetRoots .F4 1 3)) :
    SeitzExcAnisotropicF4Class 3 := by
  refine seitzExcAnisotropicF4Class_three_of_frame
    (fun K _ _ hK => frameClosing_of_detection_F4 K hK (hD K hK)) (fun K _ _ hK => ?_)
  rcases (show 4 ≤ Nat.card K ∨ Nat.card K = 3 by omega) with h4 | h3
  · exact frameNormalizerSolvable_F4 K h4
  · exact frameNormalizerSolvable_F4_three K h3

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
