module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatReduce2
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatAlt
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatOddPrime
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5PSL
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5Omega
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5Exc
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEven
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatSpor
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG Subgroup CatLeaf Equiv

section OneLayer


theorem fivePumpLeaf_holds : FivePumpLeaf :=
  fivePumpLeaf_of_clauses fivePump_alt fivePump_oddPrime
    (fun τ => by
      cases τ
      exacts [fivePump_char5_PSL, fivePump_char5_PSU, fivePump_char5_PSp,
        fivePump_char5_POmegaOdd, fivePump_char5_POmegaPlus, fivePump_char5_POmegaMinus,
        fivePump_char5_G2, fivePump_char5_F4, fivePump_char5_E6, fivePump_char5_E7,
        fivePump_char5_E8, fivePump_char5_twistedE6, fivePump_char5_trialityD4,
        fivePump_char5_vacuous _ (by decide), fivePump_char5_vacuous _ (by decide),
        fivePump_char5_vacuous _ (by decide), fivePump_char5_vacuous _ (by decide)])
    (fun τ => by
      cases τ
      exacts [fivePump_even_PSL, fivePump_even_PSU, fivePump_even_PSp,
        fivePump_even_vacuous _ (by decide), fivePump_even_POmegaPlus, fivePump_even_POmegaMinus,
        fivePump_even_exceptional _ (by decide), fivePump_even_exceptional _ (by decide),
        fivePump_even_exceptional _ (by decide), fivePump_even_exceptional _ (by decide),
        fivePump_even_exceptional _ (by decide), fivePump_even_exceptional _ (by decide),
        fivePump_even_exceptional _ (by decide), fivePump_even_exceptional _ (by decide),
        fivePump_even_vacuous _ (by decide), fivePump_even_exceptional _ (by decide),
        fivePump_even_exceptional _ (by decide)])
    (fun s => by
      by_cases h1 : s = .J1
      · subst h1; exact fivePump_spor_J1
      by_cases h2 : s = .J2
      · subst h2; exact fivePump_spor_J2
      by_cases h3 : s = .M12
      · subst h3; exact fivePump_spor_M12
      exact fivePump_spor_other s ⟨h1, h2, h3⟩)

theorem fivePumpUpInput_holds : FivePumpUpInput :=
  fivePumpUpInput_of_leaf fivePumpLeaf_holds

end OneLayer

section TwoLayers


theorem fiveTwoLayerLeaf_holds : FiveTwoLayerLeaf :=
  fiveTwoLayerLeaf_of_clauses fiveTwoLayer_alt fivePump_oddPrime fiveTwoLayer_char5
    fiveTwoLayer_even fiveTwoLayer_spor

theorem fiveTwoLayerInput_holds : FiveTwoLayerInput :=
  fiveTwoLayerInput_of_leaf fiveTwoLayerLeaf_holds

end TwoLayers

end CFSG.ComponentClassification.SolMax.FiveCat
