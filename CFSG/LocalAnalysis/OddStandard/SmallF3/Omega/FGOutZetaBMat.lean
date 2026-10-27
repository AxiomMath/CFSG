module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem zetaMatrixFacts_holds : ZetaMatrixFacts := by
  unfold ZetaMatrixFacts
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
