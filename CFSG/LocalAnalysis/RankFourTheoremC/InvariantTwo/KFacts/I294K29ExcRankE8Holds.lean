module

public import Certificates.Certificate13750
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankFourTheoremC

section Cover


theorem e8FiveFourCover_holds : E8FiveFourCover := fun q hq =>
  ExcRank.typeCover_of_typeCoverP Nat.prime_five (Certificates.certificate13750 q hq)

end Cover

section E8


theorem crossRankE8FiveFour_holds : CrossRankE8FiveFour :=
  crossRankE8FiveFour_of_cover e8FiveFourCover_holds

end E8

end CFSG.LocalAnalysis.RankFourTheoremC
