module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ClMain
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExMain
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81LieDefs
public import CFSG.Sporadic.Co2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic


theorem ds81EvenLie_holds : DS81EvenLie := by
  intro X _ _ _ _ hEven τ hτ _ _ hC
  obtain ⟨t, n, f, hadm, hm⟩ := hEven
  obtain ⟨e⟩ := hC
  have hshape := isCo2Shape_of_quotient e CFSG.Sporadic.Co2.card_Co2
  have h23 : 23 ∣ Nat.card ↥(centralizer ({τ} : Set X)) := dvd_trans (by norm_num) hshape.dvd
  have h89 : 89 ∣ Nat.card ↥(centralizer ({τ} : Set X)) := by
    by_cases ht : t ∈ classicalTags
    · exact lie23To89At_classical t ht X n f hadm hm τ hτ h23
    · exact Ex.lie23To89At_of_nonclassical ht X n f hadm hm τ hτ h23
  exact hshape.not_dvd_of_prime (p := 89) (by norm_num) (by norm_num) (by norm_num) h89

end CFSG.ComponentClassification.CatFC.DS81
