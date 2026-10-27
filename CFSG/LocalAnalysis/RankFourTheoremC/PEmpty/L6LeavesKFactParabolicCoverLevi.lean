module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicCoverMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicRadical
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactSeitzOutside

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

section CertificateInstances


theorem kFactParabolicCover_of_levi (hLevi : KFactParabolicLevi) : KFactParabolicCover :=
  kFactParabolicCover_of_inputs hLevi kFactParabolicRadical_holds kFactSeitzOutside_holds

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

end
