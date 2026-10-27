module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqEvenClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqEvenExc
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.EvenSporadicStandard.HSStd (autCentralizer)


theorem a6EvenArm_of_order (hO : LieOrderFormulasInput) : A6EvenArm := by
  intro S _ _ hS hna σ hP hσ hC hC' h129
  obtain ⟨⟨t, n, f, hadm, hm⟩, hout⟩ := hP
  cases t
  · exact a6sq_even_PSL hO hadm hm hσ hout hC hC' h129
  · exact a6sq_even_PSU hO hadm hm hσ hout hC hC' h129
  · exact a6sq_even_PSp hO hadm hm hσ hout hC hC' h129
  · exact (hadm.2.2.2 rfl).elim
  · exact a6sq_even_Omega hO (Or.inl rfl) hadm hm hσ hout hC hC' h129
  · exact a6sq_even_Omega hO (Or.inr rfl) hadm hm hσ hout hC hC' h129
  · exact a6sq_even_G2 hO hadm hm hσ hout hC hC'
  · exact a6sq_even_F4 hO hadm hm hσ hout hC hC'
  · exact a6sq_even_E6 hO hadm hm hσ hout hC hC'
  · exact a6sq_even_E7_E8 hO (Or.inl rfl) hadm hm hσ hout hC hC'
  · exact a6sq_even_E7_E8 hO (Or.inr rfl) hadm hm hσ hout hC hC'
  · exact a6sq_even_twistedE6 hO hadm hm hσ hout hC hC'
  · exact a6sq_even_trialityD4 hO hadm hm hσ hout hC hC'
  · exact a6sq_even_twistedB2 hadm hm hσ hout
  · exact absurd hadm.2.2.2.1 (by norm_num)
  · exact a6sq_even_twistedF4 hadm hm hσ hout
  · exact a6sq_even_Tits hadm hm hσ hout

end CFSG.ComponentClassification.CatFC
