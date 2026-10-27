module

public import CFSG.HardMathSupport.Dickson.BMRows.M11Holds
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SporTables3b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.MElevenFacts

set_option linter.unusedSectionVars false


theorem mElevenNoSeven_holds : SporTables.MElevenNoSeven := by
  unfold SporTables.MElevenNoSeven
  rw [CFSG.HardMathSupport.Dickson.BMRows.M11.card_centralizer_x11_holds]
  decide

theorem mElevenNo23_holds : SporTables3.MElevenNo23 := by
  unfold SporTables3.MElevenNo23
  rw [CFSG.HardMathSupport.Dickson.BMRows.M11.card_centralizer_x11_holds]
  decide

theorem mElevenNoL223_holds : SporTables3.MElevenNoL223 :=
  SporTables3.mElevenNoL223_of_no23 mElevenNo23_holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.MElevenFacts

end
