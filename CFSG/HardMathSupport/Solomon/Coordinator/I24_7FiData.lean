module

public import Certificates.Certificate13516
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Monster.B.Fischer

theorem fi22CoverData_holds :
    Fi22CoverData ↥fi22P :=
  Certificates.certificate13516

end CFSG.HardMathSupport.Solomon.Coordinator
