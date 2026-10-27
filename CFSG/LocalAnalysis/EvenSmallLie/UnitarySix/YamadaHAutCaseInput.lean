module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutCase
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5CaseCard
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Assembly
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutTheta

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaHAut


theorem caseInput : Child5.CaseInput := by
  intro G _ _ L hset hZ hQ t htL ht e
  obtain ⟨Θ, hΘ⟩ := exists_thetaSpec hset hZ hQ htL ht e
  exact hypNF_or_hypF hΘ ht fun P hP h2 => Child5.card_le_of_cent_e_norm_A₃ P hP h2

end CFSG.EvenSmallLie.UnitarySix.YamadaHAut
