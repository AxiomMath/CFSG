module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePropA

public section

namespace CFSG.ComponentClassification.Burgoyne

open CFSG.ComponentClassification.TBLit

theorem burgoyneD4TrialityConjInput_holds : BurgoyneD4TrialityConjInput := by
  intro K _ _ _ t ht
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht, pow_two] at h
  obtain ⟨β, hβ⟩ := (CatalogueBOrthogonalInvolutionConjugacy.plus_four_conjugacy (K := K)).1 t ht2
  exact ⟨β⁻¹, by rwa [inv_inv]⟩

theorem burgoynePropA_of_T2_E1_E2 (hT2 : BurgoyneD4TrialityOddCoreInput)
    (hE1 : BurgoyneExcOddCoreInput) (hE2 : BurgoynePropAE6E7) : BurgoynePropA :=
  burgoynePropA_of_inputs burgoyneD4TrialityConjInput_holds hT2 hE1 hE2

end CFSG.ComponentClassification.Burgoyne
