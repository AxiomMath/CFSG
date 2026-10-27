module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CentralAuxFinal

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


theorem twCentral (c : TwClass) (K : Type) [Field K] [Finite K] (hK : c.minQ ≤ Nat.card K)
    (D : LangLevi c.tag K c.w) : TwCentral (c.X₁ D) (c.X₂ D) :=
  CentralAux.twCentral_aux c D

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
