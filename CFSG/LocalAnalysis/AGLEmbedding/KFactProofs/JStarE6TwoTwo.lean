module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.E6TwoOrderNine
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimLieFinal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary

public section

namespace CFSG.AGLEmbedding

theorem kFactJStarElimUnitaryLie_of_schreier_ree (hSch : KFactCatalogSchreier)
    (hRee : KFactReeOrder)
    : KFactJStarElimUnitaryLie :=
  kFactJStarElimUnitaryLie_of_order_nine hSch hRee kFactUnitarySylowStructure e6TwoHasOrderNine

end CFSG.AGLEmbedding
