module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeBypass
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityA2Core

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem crossCharFamAt_trialityD4_three_of_a2CoreFreeTwo (htwo : TrialityA2CoreFreeTwo) :
    CrossCharFamAt .trialityD4 fun _ p => p = 3 :=
  crossCharFamAt_trialityD4_three_of_a2CoreFree_all (trialityA2CoreFree_of_two htwo)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
