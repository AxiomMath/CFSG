module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoRank
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimLieFinal

public section

namespace CFSG.AGLEmbedding

theorem jStarResidualD4TwoThree
    : JStarResidualD4TwoThree :=
  jStarResidualD4TwoThree_of_rank d4TwoRankTwo

theorem kFactJStarElimLie_of_e6_residual (hSch : KFactCatalogSchreier) (hRee : KFactReeOrder)
    (hE6 : JStarResidualE6TwoSix)
    : KFactJStarElimLie :=
  kFactJStarElimLie_of_residuals hSch hRee jStarResidualD4TwoThree hE6

end CFSG.AGLEmbedding
