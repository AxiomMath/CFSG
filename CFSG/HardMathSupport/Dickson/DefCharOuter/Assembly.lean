module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Classical
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Exceptional
public import CFSG.HardMathSupport.Dickson.DefCharOuter.SmallRee

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter

open CFSG.HardMathSupport.Solomon.Coordinator


theorem lieDefCharOuter_of_trialityThree (h1 : D4ThreeGraphOuter) (h2 : TrialityThreeOuter) :
    LieDefCharOuter := by
  intro S _ _ hS hnc idx he p hp hp2 hpc β hβ hout
  haveI := hS
  rcases h : CFSG.Yardstones.Md42047359a2a.lieFamily idx.1 with _ | _ | _ | _
  · exact lieDefCharOuter_classical h1 idx (Or.inl h) hnc he hp hp2 hpc hβ hout
  · exact lieDefCharOuter_classical h1 idx (Or.inr h) hnc he hp hp2 hpc hβ hout
  · exact lieDefCharOuter_exceptional h2 idx h hnc he hp hp2 hpc hβ hout
  · exact lieDefCharOuter_suzukiReeTits idx h hnc he hp hp2 hpc hβ hout

end CFSG.HardMathSupport.Dickson.DefCharOuter
