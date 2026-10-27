module

public import CFSG.LieType.SeitzGeneration.ExcOuterG2
public import CFSG.LieType.SeitzGeneration.ExcOuterTriality
public import CFSG.LieType.SeitzGeneration.ExcOuterReeF4
public import CFSG.LieType.SeitzGeneration.ExcOuterSuzuki
public import CFSG.LieType.SeitzGeneration.ExcF4Two
public import CFSG.LieType.SeitzGeneration.ExcVacuousTits

public section

namespace CFSG.LieType.SeitzGeneration

structure SeitzExcOuterNarrowResiduals : Prop where
  g2OddPower : SeitzExcOuterNarrowG2OddPower
  g2Three : SeitzExcOuterNarrowG2Three
  trialityOdd : SeitzExcOuterNarrowTrialityOdd
  trialityThree : SeitzExcOuterNarrowTrialityThree
  f4Big : SeitzExcOuterNarrowF4Big
  f4Three : SeitzExcOuterNarrowF4Three
  e6 : SeitzExcOuterNarrowE6
  twistedE6 : SeitzExcOuterNarrowTwistedE6
  e7 : SeitzExcOuterNarrowE7
  e8 : SeitzExcOuterNarrowE8
  reeG2 : SeitzExcOuterNarrowReeG2
  reeF4Three : SeitzExcOuterNarrowReeF4Three

section Assembly

theorem seitzExcOuterNarrow_of_residuals (h : SeitzExcOuterNarrowResiduals) :
    SeitzExcOuterNarrow :=
  SeitzExcOuterNarrowFamilies.toOuterNarrow
    { g2 := seitzExcOuterNarrowFor_G2_of_residuals h.g2OddPower h.g2Three
      triality := seitzExcOuterNarrowFor_triality_of_residuals h.trialityOdd h.trialityThree
      f4 := seitzExcOuterNarrowFor_F4_of_residuals h.f4Big h.f4Three
      e6 := h.e6
      twistedE6 := h.twistedE6
      e7 := h.e7
      e8 := h.e8
      suzuki := seitzExcOuterNarrowSuzuki
      reeG2 := h.reeG2
      reeF4 := seitzExcOuterNarrowFor_reeF4_of_three h.reeF4Three
      tits := seitzExcOuterNarrowFor_tits }

end Assembly

end CFSG.LieType.SeitzGeneration
