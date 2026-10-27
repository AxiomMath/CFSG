module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONLemma36
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzDBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.L34Fixed

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.L34Q8


theorem suzFixedNotLam_proved : SuzFixedNotLam := by
  intro K _ _ π hπ hker hodd hperf
  obtain ⟨ψ⟩ := nonempty_equiv_S_of_lieModel suzD_lieModel
  let πS : K →* ↥CFSG.ComponentClassification.PSL3Four.S := ψ.toMonoidHom.comp π
  have hπS : Function.Surjective πS := ψ.surjective.comp hπ
  have hkerS : πS.ker = π.ker := by
    ext x
    simp [πS, MonoidHom.mem_ker]
  have hkerc : πS.ker = center K := ker_eq_center hπS (hkerS ▸ hker)
  exact involutionFixesNotLam_eight_of_odd hperf πS hπS hkerc (hkerS ▸ hodd)

end CFSG.EvenSporadicStandard.Induction
