module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Quasi
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Central
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PureD4
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredE8Twelve
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TwelveTwoAux2

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


theorem twClosing_e8Twelve_two (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2)
    (D : LangLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w) :
    TwFrameClosing TwClass.e8Twelve.tag K (TwClass.e8Twelve.X₁ D ⊔ TwClass.e8Twelve.X₂ D) := by
  have h2 : TwClass.e8Twelve.minQ ≤ Nat.card K := by
    rw [hK]
    decide
  exact E8Two.twFrameClosing_two hK (twBasic _ K h2 D) (twQuasi_of_ne_e6Six _ (by decide) K h2 D) (twCentral _ K h2 D)
    (twCoords _ K h2 D) (twPure_D4 K h2 D) (twIrred_e8Twelve K (by omega) D)
    (E8TwoD.exists_goodC D hK E8TwoL.w_single E8TwoL.single_mem_S₁ E8TwoL.neg_single_mem_S₁)

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
