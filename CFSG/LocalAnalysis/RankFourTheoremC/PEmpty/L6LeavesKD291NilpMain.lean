module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291NilpLin
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291NilpUni

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

theorem kd291Nilp_of_tables (hGA : CFSG.Open.GriessAllModelsStatement) : KD291Nilp := by
  intro p Y _ _ P x z L hcfg hshape
  rcases hshape.model with hlin | huni
  · exact KD291N.kd291Nilp_lin hGA hcfg hlin
  · exact KD291N.kd291Nilp_uni hGA hcfg huni

section CertificateInstances


theorem kd291Nilp_holds : KD291Nilp :=
  kd291Nilp_of_tables CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
