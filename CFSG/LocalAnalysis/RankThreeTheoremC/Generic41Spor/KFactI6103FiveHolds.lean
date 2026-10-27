module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRankHolds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open


theorem kFactI6103Five_holds : KFactI6103Five := by
  intro K _ _ hq hcat h5 _
  exact Or.inl (KFactProofs.Stroth.SchurRank.schurMultiplierRankFact_holds 5 Nat.prime_five le_rfl K
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.1 hq) hcat h5)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
