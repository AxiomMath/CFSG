module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLConcrete
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLGraph
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLGraphField

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatLeafProof (GLS3OddFamilyInput)

theorem oddA6Shape_PSL (hO : LieOrderFormulasInput) (hgls : GLS3OddFamilyInput .PSL) :
    OddA6Shape .PSL :=
  oddA6Shape_PSL_of_graph hO hgls
    (fun hO _ _ _ _ _ hK hn hadm hm A hσ D hD => a6_psl_pureGraph hO hK hn hadm hm A hσ D hD)
    (fun hO _ _ _ _ _ hK hn hadm hm A σ hσ1 hord D hD =>
      a6_psl_graphField hO hK hn hadm hm A σ hσ1 hord D hD)

end CFSG.ComponentClassification.CatFC
