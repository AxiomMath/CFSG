module

public import CFSG.ClassicalInvolution.Q3.Q3OFSplitTwFin

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.Q3PP CFSG.ClassicalInvolution.Q3.Q3NS
  CFSG.Assembly.LowTwoRank

theorem twinKindsMF_of_tags (hSL : MFComp (CompData.model .PSL 4))
    (hSU : MFComp (CompData.model .PSU 4)) (hSp : MFComp (CompData.model .PSp 2))
    (hO7 : MFComp (CompData.model .POmegaOdd 3)) (hOp : MFComp (CompData.model .POmegaPlus 4))
    (hOm : MFComp (CompData.model .POmegaMinus 4)) : TwinKindsMF := by
  intro t n hlisted _
  rcases hlisted with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  exacts [hSp, hSL, hSU, hO7, hOp, hOm]

end CFSG.ClassicalInvolution.Q3.Q3OF
