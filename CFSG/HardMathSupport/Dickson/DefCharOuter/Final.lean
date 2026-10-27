module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Assembly
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.Core
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.Setup
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.GraphCorrespondence

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter

open CFSG.HardMathSupport.Solomon.Coordinator


theorem lieDefCharOuter : LieDefCharOuter :=
  lieDefCharOuter_of_trialityThree
    (TrialityChar3.d4ThreeGraphOuter_of_core TrialityChar3.trialityThreeCore_holds)
    (TrialityChar3.trialityThreeOuter_of_core TrialityChar3.trialityThreeCore_holds)

end CFSG.HardMathSupport.Dickson.DefCharOuter
