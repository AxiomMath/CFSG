module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12PrinceFin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Prince_of : Asc82Prince := by
  intro G _ _ B V H φ φ₀ hmod hvia hcompat
  exact PrinceData.conclusion ⟨hmod, hvia, hcompat⟩

end CFSG.OddStandard.SmallF3.Omega
