module

public import CFSG.LieType.SeitzGeneration.ExcOuterAssemblyV2
public import CFSG.LieType.SeitzGeneration.ExcOuterClasses

public section

namespace CFSG.LieType.SeitzGeneration

structure SeitzExcOuterNarrowResidualsV3 : Prop where
  g2OddPower : SeitzExcOuterNarrowG2OddPower
  g2Three : SeitzExcOuterNarrowG2Three
  trialityOdd : SeitzExcOuterNarrowTrialityOdd
  trialityThree : SeitzExcOuterNarrowTrialityThree
  f4LeTwo : SeitzExcOuterNarrowF4LeTwo
  e6LeTwo : SeitzExcOuterNarrowE6LeTwo
  e7LeTwo : SeitzExcOuterNarrowE7LeTwo
  e8LeTwo : SeitzExcOuterNarrowE8LeTwo
  twistedE6Three : SeitzExcOuterNarrowTwistedE6Three
  twistedE6LeTwo : SeitzExcOuterNarrowTwistedE6LeTwo
  reeG2 : SeitzExcOuterNarrowReeG2
  reeF4Three : SeitzExcOuterNarrowReeF4Three

section Convert

theorem SeitzExcOuterNarrowResidualsV3.toResidualsV2 (h : SeitzExcOuterNarrowResidualsV3) :
    SeitzExcOuterNarrowResidualsV2 where
  g2OddPower := h.g2OddPower
  g2Three := h.g2Three
  trialityOdd := h.trialityOdd
  trialityThree := h.trialityThree
  f4Big := seitzExcOuterNarrowF4Big_of_leTwo h.f4LeTwo
  e6 := seitzExcOuterNarrowE6GeFive_of_leTwo h.e6LeTwo
  twistedE6 := seitzExcOuterNarrowTwistedE6_of_classes h.twistedE6Three h.twistedE6LeTwo
  e7 := seitzExcOuterNarrowE7GeFive_of_leTwo h.e7LeTwo
  e8 := seitzExcOuterNarrowE8GeFive_of_leTwo h.e8LeTwo
  reeG2 := h.reeG2
  reeF4Three := h.reeF4Three

end Convert

section Assembly

theorem seitzExcOuterNarrow_of_residualsV3 (h : SeitzExcOuterNarrowResidualsV3) :
    SeitzExcOuterNarrow :=
  seitzExcOuterNarrow_of_residualsV2 h.toResidualsV2

end Assembly

end CFSG.LieType.SeitzGeneration
