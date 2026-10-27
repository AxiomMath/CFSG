module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Witness
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqOddRee

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Blueprint


theorem oddA6Shape_twistedG2 (hO : LieOrderFormulasInput) : OddA6Shape .twistedG2 := by
  intro S _ _ n p f hp hp2 hadm hm σ hσ D hD
  exfalso
  obtain ⟨hDc, -⟩ := hD.component
  obtain ⟨eD⟩ := hD.2.1
  have hn : n = 0 := hadm.2.2.1
  have hp3 : p = 3 := hadm.2.2.2.1
  subst hn
  subst hp3
  exact a6comp_odd_twistedG2 hO hadm hm hσ hDc eD

end CFSG.ComponentClassification.CatFC
