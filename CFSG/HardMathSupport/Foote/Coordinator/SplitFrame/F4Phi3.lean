module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.ClassesF4Detection
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Main

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.LieType.SeitzGeneration


theorem seitzExcAnisotropicF4Class_three : SeitzExcAnisotropicF4Class 3 :=
  seitzExcAnisotropicF4Class_three_of_detection fun K _ _ hK => DetectF4.frameDetection_F4 K hK

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
