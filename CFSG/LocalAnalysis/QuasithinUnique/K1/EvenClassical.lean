module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinear
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalSymplectic
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank

theorem k1_evenClassical : K1FamilyRecognition EvenClassicalFamily := by
  intro G _ _ H S U L h hP w hwU hwS hnc _
  obtain ⟨f, hf | hf | hf | hf⟩ := hP
  · exact fusionIsBenderGroup_of_stated_psl_two hf.1 hf.2
  · exact (hnc (centralizes_of_statedClassicalModel_psl h (by norm_num) hf.1 hf.2 hwU hwS)).elim
  · exact fusionIsBenderGroup_of_stated_psu_three hf.1 hf.2
  · exact (hnc (centralizes_of_statedClassicalModel_psp h hf.1 hf.2 hwU hwS)).elim

end CFSG.QuasithinUnique.K1
