module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitPointed
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFooteBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakMaximalDef

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem footePointedMaximal_of_gsWeakMaximalComponent {G : Type} [Group G] [Finite G] {a : G}
    {J : Subgroup G} (hJ : GrSLit.GSWeakMaximalComponent J) (ha : IsTwoComponentAt a J) :
    FootePointedMaximal a J :=
  ⟨ha, fun _ K hK => hJ.2 K (GrSLit.gsWeakReach_of_footeReach hK.footeReach)⟩

end CFSG.ComponentClassification.FooteLit
