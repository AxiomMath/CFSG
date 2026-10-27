module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Foote47L216

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement Pointwise

private abbrev PSL216 : Type :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)

end CFSG.ComponentClassification.Foote47L216
