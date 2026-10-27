module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieSylowLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieSylowRee
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieSylowUnitary
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Facts

public section

namespace CFSG.AGLEmbedding

theorem kFactOneLieSylowCount_of_ident
    (hId : KFactOneLieIdent) : KFactOneLieSylowCount := by
  intro K _ _ hs hnab hcat p hp hp2 T hncyc hGLB hrk
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, ⟨e⟩⟩ := hId K hs hnab hcat p hp hp2 T hncyc hGLB hrk
  rcases hd with ⟨n, hn3, hlin⟩ | ⟨hu, hf2⟩ | hree
  · obtain ⟨h1, h2⟩ := KFactProofs.OneLieSylow.card_sylow_linTwo hp2 (by omega) hlin ⟨e⟩ T
    rw [h2, h1]
  · obtain ⟨h1, h2⟩ := KFactProofs.OneLieSylow.card_sylow_unitary hu ⟨e⟩ T
    rw [h2, h1]
  · obtain ⟨rfl, -⟩ := hree.exists_eq
    obtain ⟨h1, h2⟩ := KFactProofs.OneLieSylow.card_sylow_ree hree ⟨e⟩ T
    rw [h2, h1]

end CFSG.AGLEmbedding
