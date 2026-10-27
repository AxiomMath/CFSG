module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactReduceRankOne
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieNonUnitaryLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieNonUnitaryRee

public section

namespace CFSG.AGLEmbedding

theorem kFactOneLieNonUnitary_of_ident
    (hId : KFactOneLieIdent) : KFactOneLieNonUnitary := by
  intro K _ _ hs hnab hcat p hp hp2 T hncyc hGLB hrk hU
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, ⟨e⟩⟩ := hId K hs hnab hcat p hp hp2 T hncyc hGLB hrk
  rcases hd with ⟨n, hn3, hlin⟩ | ⟨hu, -⟩ | hree
  · exact oneLieFacts_of_data hp (fun T' =>
      KFactProofs.NonUnitary.smallRankOneData_of_isLinTwo hp2 (by omega) hlin ⟨e⟩ T') T
  · exact absurd ⟨d, hu, ⟨e⟩⟩ hU
  · obtain ⟨rfl, -⟩ := hree.exists_eq
    exact KFactProofs.NonUnitary.oneLieFacts_ree hree ⟨e⟩ T

end CFSG.AGLEmbedding
