module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTwelveThirteenKer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenInputsHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineNineOneHolds
public import CFSG.GroupTheory.CoprimeLiftElementaryAbelian
public import CFSG.GroupTheory.GL52.SylowTools
public import CFSG.GroupTheory.RegularModuleThree
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Rest
public import CFSG.LieType.OutStructureLinearDiagonal
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Weak
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SevenFourTwoOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACz
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Alt
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSU
public import CFSG.RankThree.PartTwo.KFacts.K71OddChar

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.LocalAnalysis.RankThreeUC.AGL81C

section


theorem nineTwelveThirteenKer_holds : NineTwelveThirteenKer :=
  nineTwelveThirteenKer_of_inputs nineTenGen_holds nineNineOneInput_holds

theorem nineTwelveThirteenRankThree_holds : NineTwelveThirteenRankThree :=
  nineTwelveThirteenRankThree_of_ker nineTwelveThirteenKer_holds

end

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
