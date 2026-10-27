module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONLemma36
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.L34Fixed

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.ONSchreier CFSG.EvenSporadicStandard.L34Q8


theorem onK2FixedNotLam_proved : ONK2FixedNotLam := by
  intro K₂ _ _ hperf ⟨e⟩
  obtain ⟨ψ⟩ := CFSG.ComponentClassification.PSL3Four.nonempty_equiv_of_stated _
    lQuot_classicalModel
  obtain ⟨π, hπ, hker⟩ := exists_cover_map e ψ
  exact involutionFixesNotLam_four hperf π hπ hker

end CFSG.EvenSporadicStandard.Induction
