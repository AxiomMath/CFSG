module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding

@[expose] def NoXBlockFor (G : Type) [Group G] [Finite G] : Prop :=
  ∀ M Y : Subgroup G, GLBIsMaxTwoLocal M → Y ≤ M → IsSubnormal Y M → InClassXBlock Y → False

end CFSG.AGLEmbeddingD2

namespace CFSG.AGLEmbedding

theorem D1NoXBlock.noXBlockFor (h : D1NoXBlock) {G : Type} [Group G] [Finite G]
    (hG : D1Global G) : CFSG.AGLEmbeddingD2.NoXBlockFor G :=
  h G hG

end CFSG.AGLEmbedding
