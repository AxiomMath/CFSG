module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBHub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBPerm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBPres
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBCount
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBMat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBCorrect
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBInvert

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem zetaOmegaData_holds : ZetaOmegaData :=
  zetaOmegaData_of_frameHom zetaFrameHom_holds zetaMatrixFacts_holds

theorem zetaCore_holds : ZetaCore :=
  zetaCore_of_parts zetaPermSide_holds zetaPresentation_holds zetaLift_holds zetaCount_holds

theorem asc82FactZetaInv6_holds :
    Asc82FactZetaInv6 :=
  asc82FactZetaInv6_of_parts zetaCore_holds zetaOmegaData_holds zetaCorrect_holds
    zetaInvert_holds

end CFSG.OddStandard.SmallF3.Omega
