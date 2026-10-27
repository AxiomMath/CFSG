module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinear

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank

theorem k1_smallLinear : K1FamilyRecognition SmallLinearFamily := by
  intro G _ _ H S U L h hP w hwU hwS hnc _
  obtain ⟨n, hn, hmodel⟩ := hP
  exact (hnc (centralizes_of_statedClassicalModel_psl h (by omega) le_rfl hmodel hwU hwS)).elim

end CFSG.QuasithinUnique.K1
