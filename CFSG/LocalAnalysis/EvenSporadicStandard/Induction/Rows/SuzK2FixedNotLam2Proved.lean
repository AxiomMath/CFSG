module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONHyp31
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzDBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.L34Fixed

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.L34Q8


theorem suzK2FixedNotLam2_proved : SuzK2FixedNotLam2 := by
  intro K₂ _ _ hperf ⟨e⟩
  obtain ⟨ψ⟩ := nonempty_equiv_S_of_lieModel suzD_lieModel
  have hZ : center ↥suzD = ⊥ := center_eq_bot_of_equiv ψ
  let q : (↥suzD ⧸ center ↥suzD) ≃* ↥suzD :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  obtain ⟨π, hπ, hker⟩ := exists_cover_map (e.trans q) ψ
  exact involutionFixesNotLam2_eight hperf π hπ hker

end CFSG.EvenSporadicStandard.Induction
