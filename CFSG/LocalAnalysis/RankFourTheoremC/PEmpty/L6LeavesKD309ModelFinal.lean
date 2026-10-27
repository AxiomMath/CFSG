module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291Shape

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

section CertificateInstances


theorem kd309OrderModel_holds : KD309OrderModel :=
  kd309OrderModel_of_shape kd291LinUniShape_holds

theorem kd309MonoModel_holds : KD309MonoModel :=
  kd309MonoModel_of_shape kd291LinUniShape_holds

theorem kd309_holds : I291P65.KD309 :=
  kd309_of_lieW (kd309LieOrderW_of_model kd309OrderModel_holds)
      (kd309LieMono_of_model kd309MonoModel_holds)

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
