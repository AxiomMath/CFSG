module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporInputs
public import CFSG.Sporadic.Schreier.Co1OddInner
public import CFSG.Sporadic.Co2Schreier.FullAut

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem not_isSmallOrder_G24 : ¬ IsSmallOrder 251596800 :=
  not_isSmallOrder_of_between (q₀ := 795) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sporadicCase_Co1_of_inputs (hin : Co1LocalComponentsInput) : SporadicCase .Co1 := by
  refine sporadicCase_of_comps (fun G _ _ ⟨e⟩ t ht B hB => ?_)
    (outer_of_forall_inner fun α => ?_)
  · refine not_small_of_card_quotient ?_
    rw [(hin G e t ht B hB).1]
    exact not_isSmallOrder_G24
  · obtain ⟨g, hg⟩ := Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
      Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner α
    exact ⟨g, hg.symm⟩

end CFSG.ComponentClassification.RestrictedStd.Spor
