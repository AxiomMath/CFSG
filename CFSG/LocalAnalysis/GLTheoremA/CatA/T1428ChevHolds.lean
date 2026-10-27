module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2Down

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428


theorem t1428ChevFact_holds : T1428ChevFact := by
  intro Ω _ _ hΩ K y hK hy3 hyN hch J hJ
  exact chev2DownAt_holds (G := Ω) 3 Nat.prime_three (by norm_num) ⊤ K y (hΩ.subgroup ⊤) hK hy3 hyN hch J hJ

end CFSG.LocalAnalysis.GLTheoremA.T1428

end
