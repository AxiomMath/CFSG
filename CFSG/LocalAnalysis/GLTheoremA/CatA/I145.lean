module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.YS03Goals
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Common
public import CFSG.Yardstones.Md42047359a2a.MilestoneProof

public section

namespace CFSG.LocalAnalysis.GLTheoremA

section I145Holds


theorem input14_5Print_holds
    : Input14_5Print :=
  input14_5Print_of_gw
    (gwLBalanceClause3_of_statement CFSG.Yardstones.Md42047359a2a.lBalance_of_goals)

theorem i145UsedAt_holds
    (G : Type) [Group G] [Finite G] (p : ℕ) : I145UsedAt G p :=
  i145UsedAt_of input14_5Print_holds p

end I145Holds

end CFSG.LocalAnalysis.GLTheoremA
