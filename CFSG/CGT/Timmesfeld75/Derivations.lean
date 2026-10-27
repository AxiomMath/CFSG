module

public import CFSG.CGT.Timmesfeld75.NodeDerivation
public import CFSG.CGT.Timmesfeld75.WeaklyClosed

public section

namespace CFSG.CGT.Timmesfeld75

theorem corollaryBStmt_of_theoremAStmt (hA : TheoremAStmt) : CorollaryBStmt :=
  fun G _ _ T h => hA G T (isWC_of_corBHyp h)

theorem nodeStatement_of_theoremAStmt (hA : TheoremAStmt) : NodeStatement :=
  nodeStatement_of_corollaryB (corollaryBStmt_of_theoremAStmt hA)

end CFSG.CGT.Timmesfeld75
