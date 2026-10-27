module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ThirdLineAuxF4
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ThirdLineAuxE6
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ThirdLineAuxE8Ten
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ThirdLineAuxE8Twelve

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


theorem twThirdLine (c : TwClass) (K : Type) [Field K] [Finite K] (hK : c.minQ ≤ Nat.card K)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = c.e) :
    TwThirdLine c.tag K p := by
  cases c
  · exact ThirdLineAux.twThirdLine_f4Six K hK hp hp5 hord
  · exact ThirdLineAux.twThirdLine_e6Six K hK hp hp5 hord
  · exact ThirdLineAux.twThirdLine_e8Ten K hp hp5 hord
  · exact ThirdLineAux.twThirdLine_e8Twelve K hp hp5 hord

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
