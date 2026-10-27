module

public import CFSG.LieType.SeitzGeneration.ExcOuterAssemblyV3
public import CFSG.LieType.SeitzGeneration.ExcTwistedThreeVacuous

public section

namespace CFSG.LieType.SeitzGeneration

structure SeitzExcOuterNarrowResidualsV4 : Prop where
  g2OddPower : SeitzExcOuterNarrowG2OddPower
  g2Three : SeitzExcOuterNarrowG2Three
  trialityOdd : SeitzExcOuterNarrowTrialityOdd
  trialityThree : SeitzExcOuterNarrowTrialityThree
  f4LeTwo : SeitzExcOuterNarrowF4LeTwo
  e6LeTwo : SeitzExcOuterNarrowE6LeTwo
  e7LeTwo : SeitzExcOuterNarrowE7LeTwo
  e8LeTwo : SeitzExcOuterNarrowE8LeTwo
  twistedE6LeTwo : SeitzExcOuterNarrowTwistedE6LeTwo
  reeG2 : SeitzExcOuterNarrowReeG2
  reeF4Three : SeitzExcOuterNarrowReeF4Three

section Convert

theorem SeitzExcOuterNarrowResidualsV4.toResidualsV3 (h : SeitzExcOuterNarrowResidualsV4) :
    SeitzExcOuterNarrowResidualsV3 where
  g2OddPower := h.g2OddPower
  g2Three := h.g2Three
  trialityOdd := h.trialityOdd
  trialityThree := h.trialityThree
  f4LeTwo := h.f4LeTwo
  e6LeTwo := h.e6LeTwo
  e7LeTwo := h.e7LeTwo
  e8LeTwo := h.e8LeTwo
  twistedE6LeTwo := h.twistedE6LeTwo
  reeG2 := h.reeG2
  reeF4Three := h.reeF4Three
  twistedE6Three := seitzExcOuterNarrowTwistedE6Three_vacuous

end Convert

section Assembly

theorem seitzExcOuterNarrow_of_residualsV4 (h : SeitzExcOuterNarrowResidualsV4) :
    SeitzExcOuterNarrow :=
  seitzExcOuterNarrow_of_residualsV3 h.toResidualsV3

end Assembly

end CFSG.LieType.SeitzGeneration
