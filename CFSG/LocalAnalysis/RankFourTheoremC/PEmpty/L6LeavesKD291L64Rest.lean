module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291L64
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterHolds

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

section CertificateInstances


theorem kdL64I291_of_defChar_outerLie (hDef : KD291DefCharL) (hOuterLie : KD291OuterLie) :
    KDL64I291 :=
  kdL64I291_of_kdata hDef hOuterLie kd291OuterLin_holds kd291OuterUni_holds

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

end
