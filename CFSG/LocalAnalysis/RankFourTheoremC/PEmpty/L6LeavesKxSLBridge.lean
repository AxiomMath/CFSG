module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxBridge
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxSLCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open Subgroup

section Final


theorem s622Kx_of_inputs'
    (hL613 : L613) (hD : KFactDihedralTypeAut) (h27 : KFactReeL28)
    (hB : KFactReeBorel) (h2024 : KFact2024) (h2401 : KFact2401Three) (h2314 : KFact2314)
    (h1019 : KFact1019) (h2025 : KFact2025) (h131 : KFact131) (hgen : KFactParabolicGen)
    (h2715 : KFact2715) (hcov : KFactParabolicCover) (h2401S : KFact2401Spor)
    (hM11 : KFactSporM11) (hJ27 : KFactJ1L27) (hloc : KFactSporLocal) : S622Kx :=
  s622Kx_of_inputs hL613 hD h27 hB h2024 h2401 h2314 h1019 h2025 h131 hgen h2715 hcov h2401S
    hM11 hJ27 (kxSporadicCore_of_inputs hL613 h2401S hloc)

end Final

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
