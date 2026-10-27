module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Main
public import CFSG.LocalAnalysis.OddStandard.Seitz77MainDefs

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools

section Main



theorem seitz77_false_of_cases (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    (hA : Seitz77CaseAFalse) (hB : Seitz77CaseBFalse) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (h : Hyp G A) : False := by
  obtain ⟨d⟩ := h.exists_datum
  obtain ⟨V₁, V₂, hR⟩ := h.exists_radicals d
  refine hB G A V₁ V₂ h d hR fun W hW => ?_
  obtain ⟨X, O, Sy, Wt, P, H, hw, hout⟩ := h.seitz27 hGH d hR hW
  rcases hout with hA' | hB'
  · exact (hA G A V₁ V₂ W X O Sy Wt P h d hR hW H hw hA').elim
  · exact ⟨X, O, Sy, Wt, P, H, hw, hB'⟩

theorem seitz77SimpleL34_of_cases (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    (hA : Seitz77CaseAFalse) (hB : Seitz77CaseBFalse) : Seitz77SimpleL34 :=
  seitz77SimpleL34_of_false fun _ _ _ _ h => seitz77_false_of_cases hGH hA hB h

end Main

end CFSG.OddStandard.Seitz77
