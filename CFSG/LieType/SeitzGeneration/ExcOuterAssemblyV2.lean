module

public import CFSG.LieType.SeitzGeneration.ExcOuterAssembly
public import CFSG.LieType.SeitzGeneration.ExcOuterThreeVacuous

public section

namespace CFSG.LieType.SeitzGeneration

structure SeitzExcOuterNarrowResidualsV2 : Prop where
  g2OddPower : SeitzExcOuterNarrowG2OddPower
  g2Three : SeitzExcOuterNarrowG2Three
  trialityOdd : SeitzExcOuterNarrowTrialityOdd
  trialityThree : SeitzExcOuterNarrowTrialityThree
  f4Big : SeitzExcOuterNarrowF4Big
  e6 : SeitzExcOuterNarrowE6GeFive
  twistedE6 : SeitzExcOuterNarrowTwistedE6
  e7 : SeitzExcOuterNarrowE7GeFive
  e8 : SeitzExcOuterNarrowE8GeFive
  reeG2 : SeitzExcOuterNarrowReeG2
  reeF4Three : SeitzExcOuterNarrowReeF4Three

section Convert

theorem SeitzExcOuterNarrowResidualsV2.toResiduals (h : SeitzExcOuterNarrowResidualsV2) :
    SeitzExcOuterNarrowResiduals where
  g2OddPower := h.g2OddPower
  g2Three := h.g2Three
  trialityOdd := h.trialityOdd
  trialityThree := h.trialityThree
  f4Big := h.f4Big
  f4Three := seitzExcOuterNarrowF4Three_vacuous
  e6 := seitzExcOuterNarrowE6_of_geFive h.e6
  twistedE6 := h.twistedE6
  e7 := seitzExcOuterNarrowE7_of_geFive h.e7
  e8 := seitzExcOuterNarrowE8_of_geFive h.e8
  reeG2 := h.reeG2
  reeF4Three := h.reeF4Three

end Convert

section Assembly

theorem seitzExcOuterNarrow_of_residualsV2 (h : SeitzExcOuterNarrowResidualsV2) :
    SeitzExcOuterNarrow :=
  seitzExcOuterNarrow_of_residuals h.toResiduals

end Assembly

end CFSG.LieType.SeitzGeneration
