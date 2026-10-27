module

public import CFSG.LieType.SeitzGeneration.ExcAnisotropicAssemblyV3
public import CFSG.LieType.SeitzGeneration.ExcTwistedClasses
public import CFSG.LieType.SeitzGeneration.ExcThreeVacuous

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

structure SeitzExcAnisotropicResidualsV4 : Prop where
  g2NineFive : SeitzExcAnisotropicG2NineFive
  g2Three : SeitzExcAnisotropicG2ThreeMinus
  trialityOdd : SeitzExcAnisotropicTrialityOdd
  trialityThree : SeitzExcAnisotropicTrialityThree
  f4Phi3 : SeitzExcAnisotropicF4Class 3
  f4Phi4 : SeitzExcAnisotropicF4Class 4
  f4Phi6 : SeitzExcAnisotropicF4Class 6
  e6Phi6 : SeitzExcAnisotropicE6Class 6
  e8Phi5 : SeitzExcAnisotropicE8Class 5
  e8Phi8 : SeitzExcAnisotropicE8Class 8
  e8Phi10 : SeitzExcAnisotropicE8Class 10
  e8Phi12 : SeitzExcAnisotropicE8Class 12
  twE6Phi3 : SeitzExcAnisotropicTwistedE6Class 3
  twE6Phi4 : SeitzExcAnisotropicTwistedE6Class 4
  twE6Three : SeitzExcAnisotropicTwistedE6Three
  reeG2 : SeitzExcAnisotropicReeG2
  reeF4Three : SeitzExcAnisotropicReeF4Three

section Convert

theorem SeitzExcAnisotropicResidualsV4.toResidualsV3 (h : SeitzExcAnisotropicResidualsV4) :
    SeitzExcAnisotropicResidualsV3 where
  g2NineFive := h.g2NineFive
  g2Three := h.g2Three
  trialityOdd := h.trialityOdd
  trialityThree := h.trialityThree
  f4Phi3 := h.f4Phi3
  f4Phi4 := h.f4Phi4
  f4Phi6 := h.f4Phi6
  f4Three := seitzExcAnisotropicF4Three_vacuous
  e6Phi6 := h.e6Phi6
  e6Three := seitzExcAnisotropicE6Three_vacuous
  e7Three := seitzExcAnisotropicE7Three_vacuous
  e8Phi5 := h.e8Phi5
  e8Phi8 := h.e8Phi8
  e8Phi10 := h.e8Phi10
  e8Phi12 := h.e8Phi12
  e8Three := seitzExcAnisotropicE8Three_vacuous
  twistedE6 := seitzExcAnisotropicTwistedE6_of_classes h.twE6Phi3 h.twE6Phi4 h.twE6Three
  reeG2 := h.reeG2
  reeF4Three := h.reeF4Three

end Convert

section Assembly

theorem seitzExcAnisotropicNotG2ThreePlus_of_residualsV4 (h : SeitzExcAnisotropicResidualsV4) :
    SeitzExcAnisotropicNotG2ThreePlus :=
  seitzExcAnisotropicNotG2ThreePlus_of_residualsV3 h.toResidualsV3

end Assembly

end CFSG.LieType.SeitzGeneration
