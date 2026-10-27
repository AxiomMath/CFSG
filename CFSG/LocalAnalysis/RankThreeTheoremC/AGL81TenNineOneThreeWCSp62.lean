module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoCodes
import CFSG.CGT.PushingUpLit.Transport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.KGroups.Sp6 CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

@[expose] def cT6 : List ℕ := [1, 2, 32, 8, 16, 4]

theorem genB_cT6 : genB cT6 = true := by decide

theorem conjC_cT6_cZ : conjC cT6 cZ = mulC cZ cW2 := by decide

theorem cZ_eq : cZ = mulC cW0 (mulC cW1 cW2) := by decide

theorem not_commB_zw : commB (mulC cZ cW2) cSg = false := by decide

theorem not_commB_zw2 : commB (mulC (mulC cZ cW2) (mulC cZ cW2)) cSg = false := by decide

theorem genB_cSg : genB cSg = true := by decide

theorem genB_cW2 : genB cW2 = true := by decide

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
