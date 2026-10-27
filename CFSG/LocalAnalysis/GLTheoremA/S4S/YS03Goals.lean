module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4

theorem gwLBalanceClause3_of_statement
    (h : CFSG.Open.LBalanceStatement) : GWLBalanceClause3 := by
  intro X _ _ hK p hp P hP
  exact (h X hK p hp P hP).2.2

end CFSG.LocalAnalysis.GLTheoremA
