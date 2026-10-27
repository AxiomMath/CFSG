module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallGraph3
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallGraph4

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

theorem oddA6Small_PSL (hO : LieOrderFormulasInput) : OddA6Small .PSL :=
  oddA6Small_PSL_of_graph hO
    (PSLSmall.pureGraphSmall_of_three_four
      (fun hK hs A hσ D hD => a6_psl_pureGraph_small_three hO hK hs A hσ D hD)
      (fun hK hs A hσ D hD => a6_psl_pureGraph_small_four hO hK hs A hσ D hD))

end CFSG.ComponentClassification.CatFC
