module

public import CFSG.LocalAnalysis.OddStandard.ChildL34
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def L34EvenSylowStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    LieModel (L ⧸ center L) .PSL 3 2 2 → Even (Nat.card (center L)) →
    ∀ R : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (R : Subgroup (centralizer (L : Set G))) →
        ∃ (S : Sylow 2 G) (T : Sylow 2 NativeSporadic.ON),
          Nonempty ((S : Subgroup G) ≃* (T : Subgroup NativeSporadic.ON))

theorem l34CyclicEvenCenter_of_sylowStep (h : L34EvenSylowStep)
    (hON : ComponentClassification.GrSLit.ONanSylowInput) : L34CyclicEvenCenter := by
  intro G _ _ L hS h34 hev R hR
  have := hS.simple
  obtain ⟨S, T, e⟩ := h G L hS h34 hev R hR
  exact hON G hS.nonab hS.kProper S T e

end CFSG.OddStandard
