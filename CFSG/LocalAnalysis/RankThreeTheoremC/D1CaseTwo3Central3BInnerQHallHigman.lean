module

public import CFSG.GroupTheory.SteinbergCBFTPSolvable
import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG.HallHigman

namespace InnerQ.HallHigman

variable {Q : Type} [Group Q] [Finite Q] {p : ℕ} [hp : Fact p.Prime]

theorem IsPSolvable.quotient' (h : IsPSolvable p Q) (N : Subgroup Q) [N.Normal] :
    IsPSolvable p (Q ⧸ N) :=
  CFSG.GroupTheory.FT63ChII.isPSolvable_of_isPiSeparable
    ((isPiSeparable_of_isPSolvable hp.out h).quotient N)

theorem IsPSolvable.subgroup' (h : IsPSolvable p Q) (K : Subgroup Q) : IsPSolvable p K :=
  CFSG.GroupTheory.FT63ChII.isPSolvable_of_isPiSeparable
    ((isPiSeparable_of_isPSolvable hp.out h).subgroup K)

end InnerQ.HallHigman

end CFSG.LocalAnalysis.RankThreeTheoremC
