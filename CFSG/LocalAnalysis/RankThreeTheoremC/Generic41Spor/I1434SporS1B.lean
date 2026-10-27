module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434SporS1Base
public import CFSG.Monster.B.Pinned.Primes.FiveRelations

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434

open CFSG.Blueprint CFSG.Monster.B.Pinned

theorem b_hasNonabelianFiveSubgroup :
    HasNonabelianFiveSubgroup NativeSporadic.B := by
  obtain ⟨-, -, -, -, -, -, -, hq, hz5, hz1, hqz, -⟩ := five_facts
  exact hasNonabelianFiveSubgroup_of_heis
    (SporS1.heisRel_of_bcomm (hq 0).1 (hq 1).1 hz5 (hqz 0) (hqz 1) rfl) hz1

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434
