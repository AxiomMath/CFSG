module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointTypes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth

open CFSG.LocalAnalysis.RankThreeTheoremC

theorem kFactComponentPCoreThree_of_general
    (h : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial) :
    KFactComponentPCoreThree := by
  intro X _ _ hX R K hR hK hKR
  exact h X hX 3 R K Nat.prime_three (by norm_num) hR hK hKR

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth
