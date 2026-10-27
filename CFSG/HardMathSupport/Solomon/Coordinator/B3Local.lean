module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Catalog
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremB.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem isKGroup_of_openIsKGroup {X : Type} [Group X] [Finite X] (h : CFSG.Open.IsKGroup X) :
    CFSG.IsKGroup X :=
  CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
    CFSG.Assembly.inCatalog_containsAbelianSimple h

end CFSG.HardMathSupport.Solomon.Coordinator
