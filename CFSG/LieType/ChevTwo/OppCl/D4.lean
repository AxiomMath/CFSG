module

public import CFSG.LieType.ChevTwo.OppCl.D4Main
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open

section D4

theorem oppositeFixed_POmegaPlus_four (F : Type) [Field F] [Finite F] [CharP F 2] :
    OppositeFixed (StatedProj (StatedOmega (StatedQuadPlus 4 F))) := by
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup F
  exact oppositeFixed_of_mulEquiv e CFSG.LieType.ChevTwo.Semi.oppositeFixed_adjointGroup_D4

end D4

end CFSG.LieType.ChevTwo.OppCl
