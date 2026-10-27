module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10F2315a
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzEvenCentreCases
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzEvenCentreD4F4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzEvenCentreU6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzEvenCentreE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.KRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Certs


theorem seitzEvenCentre_of_kRank (hk : Rk2KRank) : SeitzEvenCentre := by
  intro K _ _ hL q hq hq2 hZ h4
  obtain ⟨lab, hK⟩ := exists_isLabel_of_hasLabel hL
  have h4' : 4 ≤ rk2Mult lab (rk2Ord q lab.n) := h4.trans (hk K lab q hK hq hq2)
  obtain ⟨hq3, hcases⟩ := seitzEvenCentre_cases hK hq hq2 hZ h4'
  subst hq3
  rcases hcases with rfl | rfl | rfl | rfl
  · exact seitzEvenCentre_D4 hK
  · exact seitzEvenCentre_F4 hK
  · exact seitzEvenCentre_twA5 hK
  · exact seitzEvenCentre_twE6 hK

section RankTable


theorem seitzEvenCentre_holds : SeitzEvenCentre := seitzEvenCentre_of_kRank rk2KRank

end RankTable

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
