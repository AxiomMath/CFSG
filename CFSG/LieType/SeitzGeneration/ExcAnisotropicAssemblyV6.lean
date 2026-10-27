module

public import CFSG.LieType.SeitzGeneration.ExcAnisotropicAssemblyV5
public import CFSG.LieType.SeitzGeneration.ExcTwistedThreeVacuous

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

structure SeitzExcAnisotropicResidualsV6 : Prop where
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
  reeF4Three : SeitzExcAnisotropicReeF4Three

section Convert

theorem SeitzExcAnisotropicResidualsV6.toResidualsV5 (h : SeitzExcAnisotropicResidualsV6) :
    SeitzExcAnisotropicResidualsV5 where
  g2NineFive := h.g2NineFive
  g2Three := h.g2Three
  trialityOdd := h.trialityOdd
  trialityThree := h.trialityThree
  f4Phi3 := h.f4Phi3
  f4Phi4 := h.f4Phi4
  f4Phi6 := h.f4Phi6
  e6Phi6 := h.e6Phi6
  e8Phi5 := h.e8Phi5
  e8Phi8 := h.e8Phi8
  e8Phi10 := h.e8Phi10
  e8Phi12 := h.e8Phi12
  twE6Phi3 := h.twE6Phi3
  twE6Phi4 := h.twE6Phi4
  reeF4Three := h.reeF4Three
  twE6Three := seitzExcAnisotropicTwistedE6Three_vacuous

end Convert

section Assembly

theorem seitzExcAnisotropicNotG2ThreePlus_of_residualsV6 (h : SeitzExcAnisotropicResidualsV6) :
    SeitzExcAnisotropicNotG2ThreePlus :=
  seitzExcAnisotropicNotG2ThreePlus_of_residualsV5 h.toResidualsV5

end Assembly

end CFSG.LieType.SeitzGeneration
