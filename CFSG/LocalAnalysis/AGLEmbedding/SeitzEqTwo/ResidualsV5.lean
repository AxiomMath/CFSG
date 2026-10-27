module

public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.Fields
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.Twisted
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzCyc.ExcCyc
import CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator.Closed
import CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator.Handback
import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddMain
import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.OuterThreeAll
public import CFSG.LieType.SeitzGeneration.ExcOuterAssemblyV5

public section

namespace CFSG.AGLEmbedding.SeitzCyc

open CFSG.LieType.SeitzGeneration


theorem SeitzExcOuterCycResiduals.toV5 (h : SeitzExcOuterCycResiduals) :
    SeitzExcOuterNarrowResidualsV5 := by
  exact
    { g2OddPower :=
        CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator.seitzExcOuterNarrowG2OddPower_proved
      g2Three := CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator.seitzExcOuterNarrowG2Three_proved
      trialityOdd := HardMathSupport.Seitz.TrialityOdd.seitzExcOuterNarrowTrialityOdd_of_pair
          HardMathSupport.Seitz.TrialityOdd.subfieldPairD4Odd_proof
      trialityThree :=
        CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.seitzExcOuterNarrowTrialityThree_proved
      f4EqTwo := SeitzEqTwo.seitzExcOuterNarrowF4EqTwo_holds
      f4LeOne := h.f4LeOne
      e6EqTwo := SeitzEqTwo.seitzExcOuterNarrowE6EqTwo_holds
      e6LeOne := h.e6LeOne
      e7EqTwo := SeitzEqTwo.seitzExcOuterNarrowE7EqTwo_holds
      e7LeOne := h.e7LeOne
      e8EqTwo := SeitzEqTwo.seitzExcOuterNarrowE8EqTwo_holds
      e8LeOne := h.e8LeOne
      twistedE6EqTwo := SeitzEqTwo.seitzExcOuterNarrowTwistedE6EqTwo_holds
      twistedE6LeOne := h.twistedE6LeOne
      reeG2 := h.reeG2
      reeF4Three := h.reeF4Three }

end CFSG.AGLEmbedding.SeitzCyc
