module

public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs
public import CFSG.LocalAnalysis.GL83PartI.I_20_1

public section

namespace CFSG.LocalAnalysis.GLTheoremB

theorem input20_1_proved : Input20_1 := fun X _ _ p hp hp2 hlayer B hB =>
  GL83.I_20_1_proved X p hp hp2 hlayer B hB.2.1 (fun E hE hBE => hB.2.2 E le_top hE hBE)

end CFSG.LocalAnalysis.GLTheoremB
