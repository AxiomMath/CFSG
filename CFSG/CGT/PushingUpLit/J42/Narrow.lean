module

public import CFSG.CGT.PushingUpLit.SolK.TI
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.GH74
open CFSG.Assembly (InCatalog KProper)

@[expose] def JankoU42Gen4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M X : Subgroup G) (S : SolCfg G M X 2),
    KProper InCatalog G → TightData S → RSmall S → ¬ CentInM S → SectionalTwoRankLE G 4

end CFSG.CGT.PushingUpLit.SolK
