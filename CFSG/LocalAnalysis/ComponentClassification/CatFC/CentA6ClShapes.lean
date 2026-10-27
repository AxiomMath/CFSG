module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClAll
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSL
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSU
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSp
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaMinus
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaPlus
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExcG2
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExcF4
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExcE8
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExc2Main
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExc3
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClRee

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeafProof (GLS3OddFamilyInput)


theorem a6glsFamily_of_input (h : CatLeaf.GLS3OddLieAutComponentsInput) (t : StatedLieTag) :
    GLS3OddFamilyInput t :=
  fun J _ n p f hp hp2 hadm hm => h J t n p f hp hp2 hadm hm

theorem oddA6Shape_of_inputs (hO : CatLeaf.LieOrderFormulasInput)
    (hgls : CatLeaf.GLS3OddLieAutComponentsInput) : ∀ t, OddA6Shape t :=
  oddA6Shape_all
    (oddA6Shape_PSL hO (a6glsFamily_of_input hgls _))
    (oddA6Shape_PSU hO (a6glsFamily_of_input hgls _))
    (oddA6Shape_PSp hO (a6glsFamily_of_input hgls _))
    (oddA6Shape_POmegaOdd hO (a6glsFamily_of_input hgls _))
    (oddA6Shape_POmegaPlus hO (a6glsFamily_of_input hgls _))
    (oddA6Shape_POmegaMinus hO (a6glsFamily_of_input hgls _))
    (oddA6Shape_G2 hO (a6glsFamily_of_input hgls _))
    (oddA6Shape_F4 hO (a6glsFamily_of_input hgls _))
    (oddA6Shape_E6 hO (a6glsFamily_of_input hgls _))
    (oddA6Shape_E7 hO (a6glsFamily_of_input hgls _))
    (oddA6Shape_E8 hO (a6glsFamily_of_input hgls _))
    (oddA6Shape_twistedE6 hO (a6glsFamily_of_input hgls _))
    (oddA6Shape_trialityD4 hO (a6glsFamily_of_input hgls _))
    (oddA6Shape_twistedG2 hO)

end CFSG.ComponentClassification.CatFC
