module

public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.TwoModuloExtension

variable {X : Type*} [Group X]

section Solvable

variable [Finite X]

theorem perfectResidual_le_of_isSolvable_quotient {N : Subgroup X} [N.Normal]
    (h : Group.IsSolvable (X ⧸ N)) : CFSG.perfectResidual X ≤ N :=
  ((CFSG.perfect_residual_characterization (G := X)).2.2.2.2.1 N).1 h

end Solvable

end CFSG.GroupTheory.CoprimeActionSupport.TwoModuloExtension
