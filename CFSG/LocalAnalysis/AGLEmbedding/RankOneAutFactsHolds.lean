module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactsFamiliesNarrow
public import CFSG.LocalAnalysis.AGLEmbedding.RankOneAutFactsLin
public import CFSG.LocalAnalysis.AGLEmbedding.RankOneAutFactsUnitary
public import CFSG.LocalAnalysis.AGLEmbedding.RankOneAutFactsRee

public section

namespace CFSG.AGLEmbedding

theorem rankOneAutFactsFamilies_holds :
    RankOneAutFactsFamilies := by
  intro K _ _ p hp hp2 d hd he
  rcases hd with ⟨n, hn, hdn⟩ | ⟨hu, -⟩ | hr
  · have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have h27 : 3 ^ 3 ≤ p ^ n :=
      (Nat.pow_le_pow_left hp3 3).trans (Nat.pow_le_pow_right hp.pos hn)
    exact RankOneAut.rankOneLieAutFacts_linTwo hp hp2 (by omega) (by omega) hdn he
  · exact RankOneAut.rankOneLieAutFacts_unitary hp2 hu he
  · obtain ⟨hp3, hm⟩ := hr
    subst hp3
    exact RankOneAut.rankOneLieAutFacts_ree ⟨rfl, hm⟩ he

end CFSG.AGLEmbedding
