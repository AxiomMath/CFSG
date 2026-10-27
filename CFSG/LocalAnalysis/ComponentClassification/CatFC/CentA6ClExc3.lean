module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExc3Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExc3TriOuter
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExc3E6Outer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section TwistedE6


theorem oddA6Shape_twistedE6 (hO : LieOrderFormulasInput)
    (_hgls : GLS3OddFamilyInput .twistedE6) : OddA6Shape .twistedE6 := by
  intro S _ _ n p f hp hp2 hadm hm σ hσ D hD
  exfalso
  obtain rfl : n = 0 := hadm.2.2
  by_cases hi : σ ∈ (MulAut.conj : S →* MulAut S).range
  · exact a6_twistedE6_inner_false hp hp2 hadm hm hσ hi hD
  · exact a6_twistedE6_outer_false hO hp hp2 hadm hm hσ hi hD

end TwistedE6

section TrialityD4


theorem oddA6Shape_trialityD4 (hO : LieOrderFormulasInput)
    (_hgls : GLS3OddFamilyInput .trialityD4) : OddA6Shape .trialityD4 := by
  intro S _ _ n p f hp hp2 hadm hm σ hσ D hD
  exfalso
  obtain rfl : n = 0 := hadm.2.2
  by_cases hi : σ ∈ (MulAut.conj : S →* MulAut S).range
  · exact a6_trialityD4_inner_false hp hp2 hadm hm hσ hi hD
  · exact a6_trialityD4_outer_false hO hp hp2 hadm hm hσ hi hD

end TrialityD4

end CFSG.ComponentClassification.CatFC
