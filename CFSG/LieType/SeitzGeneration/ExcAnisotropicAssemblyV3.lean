module

public import CFSG.LieType.SeitzGeneration.ExcAnisotropicAssembly
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicClasses

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

structure SeitzExcAnisotropicResidualsV3 : Prop where
  g2NineFive : SeitzExcAnisotropicG2NineFive
  g2Three : SeitzExcAnisotropicG2ThreeMinus
  trialityOdd : SeitzExcAnisotropicTrialityOdd
  trialityThree : SeitzExcAnisotropicTrialityThree
  f4Phi3 : SeitzExcAnisotropicF4Class 3
  f4Phi4 : SeitzExcAnisotropicF4Class 4
  f4Phi6 : SeitzExcAnisotropicF4Class 6
  f4Three : SeitzExcAnisotropicF4Three
  e6Phi6 : SeitzExcAnisotropicE6Class 6
  e6Three : SeitzExcAnisotropicE6Three
  e7Three : SeitzExcAnisotropicE7Three
  e8Phi5 : SeitzExcAnisotropicE8Class 5
  e8Phi8 : SeitzExcAnisotropicE8Class 8
  e8Phi10 : SeitzExcAnisotropicE8Class 10
  e8Phi12 : SeitzExcAnisotropicE8Class 12
  e8Three : SeitzExcAnisotropicE8Three
  twistedE6 : SeitzExcAnisotropicTwistedE6
  reeG2 : SeitzExcAnisotropicReeG2
  reeF4Three : SeitzExcAnisotropicReeF4Three

section Convert

theorem SeitzExcAnisotropicResidualsV3.toResiduals (h : SeitzExcAnisotropicResidualsV3) :
    SeitzExcAnisotropicResiduals where
  g2NineFive := h.g2NineFive
  g2Three := h.g2Three
  trialityOdd := h.trialityOdd
  trialityThree := h.trialityThree
  f4Big := seitzExcAnisotropicF4Big_of_classes h.f4Phi3 h.f4Phi4 h.f4Phi6
  f4Three := h.f4Three
  e6 := seitzExcAnisotropicE6_of_classes h.e6Phi6 h.e6Three
  twistedE6 := h.twistedE6
  e7 := seitzExcAnisotropicE7_of_three h.e7Three
  e8 := seitzExcAnisotropicE8_of_classes h.e8Phi5 h.e8Phi8 h.e8Phi10 h.e8Phi12 h.e8Three
  reeG2 := h.reeG2
  reeF4Three := h.reeF4Three

end Convert

section Assembly

theorem seitzExcAnisotropicNotG2ThreePlus_of_residualsV3 (h : SeitzExcAnisotropicResidualsV3) :
    SeitzExcAnisotropicNotG2ThreePlus :=
  seitzExcAnisotropicNotG2ThreePlus_of_residuals h.toResiduals

end Assembly

end CFSG.LieType.SeitzGeneration
