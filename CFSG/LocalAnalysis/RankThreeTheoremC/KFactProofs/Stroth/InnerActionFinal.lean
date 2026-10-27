module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionLie
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionN1Linear
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionN1Unitary
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionN1D4
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionSP3
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionN1Exceptional

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction

section Final


theorem kFactInnerAction_holds : KFactInnerAction :=
  kFactInnerAction_of_residues n1PSL_holds n1PSU_holds Exceptional.n1E6_holds
      Exceptional.n1TwE6_holds n1D4_holds Exceptional.n13D4_holds sp3PSL_holds sp3PSU_holds

end Final

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction
