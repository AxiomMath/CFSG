module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Classes

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


theorem seitzExcAnisotropicF4Class_six : SeitzExcAnisotropicF4Class 6 :=
  seitzExcAnisotropicF4Class_six_of_leaves twClassLeaves_f4Six

theorem seitzExcAnisotropicE6Class_six : SeitzExcAnisotropicE6Class 6 :=
  seitzExcAnisotropicE6Class_six_of_leaves twClassLeaves_e6Six

section E8Ten


theorem seitzExcAnisotropicE8Class_ten : SeitzExcAnisotropicE8Class 10 :=
  seitzExcAnisotropicE8Class_ten_of_leaves twClassLeaves_e8Ten

end E8Ten

theorem seitzExcAnisotropicE8Class_twelve : SeitzExcAnisotropicE8Class 12 :=
  seitzExcAnisotropicE8Class_twelve_of_leaves twClassLeaves_e8Twelve

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
