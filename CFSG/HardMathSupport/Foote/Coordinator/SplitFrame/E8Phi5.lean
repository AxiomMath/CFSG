module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.ClassesE8Detection
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Main
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.N2

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.LieType.SeitzGeneration


theorem seitzExcAnisotropicE8Class_five : SeitzExcAnisotropicE8Class 5 :=
  seitzExcAnisotropicE8Class_five_of_detection (fun K _ _ => DetectE8.frameDetection_E8 K)
    fun K _ _ hK => DetectE8.frameNormalizerSolvable_E8_two K hK

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
