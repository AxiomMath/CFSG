module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard

@[expose] def OddMultThree (s : TauCeti.SporadicName) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → Odd (Nat.card (center L)) →
    IsSporadic (L ⧸ center L) s → Nat.card (center L) ∣ 3

variable {s : TauCeti.SporadicName} {H : Type} [Group H] [Finite H] {L : Subgroup H}

theorem OddCover.card_center_dvd_three (hmult : OddMultThree s) (h : OddCover s L) :
    Nat.card (center ↥L) ∣ 3 :=
  hmult ↥L h.1 h.2.1 h.2.2

end CFSG.EvenSporadicStandard.Induction
