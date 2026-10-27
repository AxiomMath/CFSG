module

public import CFSG.LocalAnalysis.OddStandard.ONanDefs
public import CFSG.LocalAnalysis.OddStandard.L34EvenSylowBal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def StageU (N : Type) [Group N] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper Blueprint.Catalog G →
    ∀ (S : Sylow 2 G) (T : Sylow 2 N),
      Nonempty ((S : Subgroup G) ≃* (T : Subgroup N)) → Balanced G

theorem onanSylowInput_of_bal (hB : SylowBal NativeSporadic.ON) (hU : StageU NativeSporadic.ON) :
    ComponentClassification.GrSLit.ONanSylowInput := by
  intro G _ _ _ hna hK S T e
  exact hB G hna (hU G hna hK S T e) S T e

theorem l34CyclicEvenCenterBal_of_sylowStepBal' (h : CFSG.OddStandard.L34EvenSylowStepBal)
    (hON : SylowBal NativeSporadic.ON) : CFSG.OddStandard.L34CyclicEvenCenterBal := by
  intro G _ _ L hS hbal h34 hev R hR
  have := hS.simple
  obtain ⟨S, T, e⟩ := h G L hS hbal h34 hev R hR
  exact hON G hS.nonab hbal S T e

end CFSG.OddStandard.ONanRec
