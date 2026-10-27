module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Ambient3
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34Only
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

theorem D2Amb3.of_setting {G : Type} [Group G] [Finite G] (hS : Setting G) (hD1 : TheoremD1 G)
    (hp : 3 ∈ rankThreeSigmaA G) : D2Amb3 G :=
  ⟨aglGlobal_of_setting hS, d1At_of_theoremD1 hD1 hp⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
