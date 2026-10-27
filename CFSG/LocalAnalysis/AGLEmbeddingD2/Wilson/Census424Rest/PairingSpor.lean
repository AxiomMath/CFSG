module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.PairingM24
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.PairingHe
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofPairing
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.PairingDich

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census424Rest

open CFSG CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint

theorem k424PairingSpor_holds :
    K424PairingSpor := by
  intro X _ _ hX D c d K h
  rcases hX with hX | hX
  · obtain ⟨e⟩ := hX
    exact pairing_of_dichotomy (fun c' hc3 => m24_dichotomy e c' hc3) h
  · obtain ⟨e⟩ := hX
    exact pairing_of_dichotomy
      (fun c' hc3 => he_dichotomy (e.trans CFSG.Sporadic.HeldB.heEquivP) c' hc3) h

end CFSG.AGLEmbeddingD2.Wilson.Census424Rest
