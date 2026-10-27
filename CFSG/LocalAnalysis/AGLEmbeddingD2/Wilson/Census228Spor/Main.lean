module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.M11
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.J2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.J3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.McL
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.ON
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSpor

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census228Spor

open CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint

theorem census228SporData_holds :
    Census228SporData := by
  intro s hs
  simp only [sporadicsData228, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact threeFiveData228_M11
  · exact threeFiveData228_M12
  · exact threeFiveData228_J2
  · exact threeFiveData228_J3
  · exact threeFiveData228_McL
  · exact threeFiveData228_ON

end CFSG.AGLEmbeddingD2.Wilson.Census228Spor
