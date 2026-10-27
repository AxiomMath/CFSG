module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OddCentre
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PermJordan
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3SolvableStrong
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.BridgeAbstract

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.AGLEmbeddingD2.McLaughlin CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

structure D2Leaves3SX (G : Type) [Group G] [Finite G] : Prop where
  l34MSolvable : D2L34BetaMSolvableStrong3 G

variable {G : Type} [Group G] [Finite G]

end CFSG.LocalAnalysis.RankThreeTheoremC
