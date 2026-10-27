module

public import CFSG.LieType.SeitzGeneration.ExcOuterAssemblyV4
public import CFSG.LieType.SeitzGeneration.ExcOuterSplit

public section

namespace CFSG.LieType.SeitzGeneration

structure SeitzExcOuterNarrowResidualsV5 : Prop where
  g2OddPower : SeitzExcOuterNarrowG2OddPower
  g2Three : SeitzExcOuterNarrowG2Three
  trialityOdd : SeitzExcOuterNarrowTrialityOdd
  trialityThree : SeitzExcOuterNarrowTrialityThree
  f4EqTwo : SeitzExcOuterNarrowF4EqTwo
  f4LeOne : SeitzExcOuterNarrowF4LeOne
  e6EqTwo : SeitzExcOuterNarrowE6EqTwo
  e6LeOne : SeitzExcOuterNarrowE6LeOne
  e7EqTwo : SeitzExcOuterNarrowE7EqTwo
  e7LeOne : SeitzExcOuterNarrowE7LeOne
  e8EqTwo : SeitzExcOuterNarrowE8EqTwo
  e8LeOne : SeitzExcOuterNarrowE8LeOne
  twistedE6EqTwo : SeitzExcOuterNarrowTwistedE6EqTwo
  twistedE6LeOne : SeitzExcOuterNarrowTwistedE6LeOne
  reeG2 : SeitzExcOuterNarrowReeG2
  reeF4Three : SeitzExcOuterNarrowReeF4Three

theorem SeitzExcOuterNarrowResidualsV5.toResidualsV4 (h : SeitzExcOuterNarrowResidualsV5) :
    SeitzExcOuterNarrowResidualsV4 where
  g2OddPower := h.g2OddPower
  g2Three := h.g2Three
  trialityOdd := h.trialityOdd
  trialityThree := h.trialityThree
  f4LeTwo := seitzExcOuterNarrowForAt_leTwo_of_split h.f4EqTwo h.f4LeOne
  e6LeTwo := seitzExcOuterNarrowForAt_leTwo_of_split h.e6EqTwo h.e6LeOne
  e7LeTwo := seitzExcOuterNarrowForAt_leTwo_of_split h.e7EqTwo h.e7LeOne
  e8LeTwo := seitzExcOuterNarrowForAt_leTwo_of_split h.e8EqTwo h.e8LeOne
  twistedE6LeTwo := seitzExcOuterNarrowForAt_leTwo_of_split h.twistedE6EqTwo h.twistedE6LeOne
  reeG2 := h.reeG2
  reeF4Three := h.reeF4Three

section Assembly

theorem seitzExcOuterNarrow_of_residualsV5 (h : SeitzExcOuterNarrowResidualsV5) :
    SeitzExcOuterNarrow :=
  seitzExcOuterNarrow_of_residualsV4 h.toResidualsV4

end Assembly

end CFSG.LieType.SeitzGeneration
