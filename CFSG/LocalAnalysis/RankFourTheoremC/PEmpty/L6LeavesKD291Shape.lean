module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291Model
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291Zero

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

section CertificateInstances


theorem kd291LinUniShape_holds :
    ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y) (L : Subgroup Y),
      LinUniCfg p P x z L → LinUniShape p x L :=
  fun p Y _ _ P x z L h =>
    ⟨kd291LinUniZero_holds p Y P x z L h, kd291LinUniModel_holds p Y P x z L h⟩

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
