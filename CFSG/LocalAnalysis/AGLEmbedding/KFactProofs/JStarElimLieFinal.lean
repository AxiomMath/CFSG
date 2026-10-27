module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimLie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimUnitaryLie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SpFourEightRank

public section

namespace CFSG.AGLEmbedding

theorem kFactJStarElimLie_of_residuals (hSch : KFactCatalogSchreier) (hRee : KFactReeOrder)
    (hD4 : JStarResidualD4TwoThree) (hE6 : JStarResidualE6TwoSix)
    

    : KFactJStarElimLie :=
  kFactJStarElimLie_of hSch hRee hD4 jStarResidualSp48Three hE6

theorem kFactJStarElimUnitaryLie_of_order_nine (hSch : KFactCatalogSchreier)
    (hRee : KFactReeOrder) (hKU2 : KFactUnitarySylowStructure) (h9 : E6TwoHasOrderNine)
    

    : KFactJStarElimUnitaryLie :=
  kFactJStarElimUnitaryLie_of hSch hRee (jStarResidualE6TwoTwo_of_order_nine hKU2 h9)

end CFSG.AGLEmbedding
