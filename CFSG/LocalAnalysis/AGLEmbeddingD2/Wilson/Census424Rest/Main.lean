module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.J3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.McL
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.M12
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.J2

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census424Rest

open CFSG CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint

theorem k424Inner46FiveRest_holds :
    K424Inner46FiveRest := by
  intro X _ _ h
  rcases h with h | h | h | h
  · obtain ⟨e⟩ := h
    exact census424_of_m12 e
  · obtain ⟨e⟩ := h
    exact census424_of_j2 e
  · obtain ⟨e⟩ := h
    exact census424_of_j3 e
  · obtain ⟨e⟩ := h
    exact census424_of_mcl e

end CFSG.AGLEmbeddingD2.Wilson.Census424Rest
