module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG CFSG.Blueprint CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

theorem card_of_lieModel_PSU_six_two {X : Type} [Group X] {f : ℕ}
    (h : LieModel X .PSU 6 2 f) : Nat.card X = ordTwistedA 5 (2 ^ f) :=
  UnitaryPilot.card_of_lieModel_PSU_two_pow h

theorem card_of_lieModel_POmegaMinus_four_two {X : Type} [Group X] {f : ℕ}
    (h : LieModel X .POmegaMinus 4 2 f) : Nat.card X = ordTwistedD 4 (2 ^ f) :=
  OmegaPilot.card_of_lieModel_POmega_two (Or.inr rfl) h

theorem ordTwistedA_five_two_eq : ordTwistedA 5 (2 ^ 1) = 9196830720 := by decide

section Orders

theorem lieModel_PSU_six_two_unique_of_card_eq {X Y : Type} [Group X] [Group Y] {f : ℕ}
    (h6 : LieModel X .PSU 6 2 f) {t : StatedLieTag} {n f' : ℕ} (h : LieModel Y t n 2 f')
    (hcard : Nat.card Y = Nat.card X) : t = .PSU ∧ n = 6 ∧ f' = f :=
  UnitaryPilot.lieModel_PSU_two_unique_of_card_eq (by norm_num) h6 h hcard

theorem lieModel_PSU_six_two_unique {X : Type} [Group X] {f f' : ℕ} {t : StatedLieTag} {n : ℕ}
    (h : LieModel X .PSU 6 2 f) (h' : LieModel X t n 2 f') : t = .PSU ∧ n = 6 ∧ f' = f :=
  lieModel_PSU_six_two_unique_of_card_eq h h' rfl

theorem lieModel_POmegaMinus_four_two_unique_of_card_eq {X Y : Type} [Group X] [Group Y] {f : ℕ}
    (h8 : LieModel X .POmegaMinus 4 2 f) {t : StatedLieTag} {n f' : ℕ} (h : LieModel Y t n 2 f')
    (hcard : Nat.card Y = Nat.card X) : t = .POmegaMinus ∧ n = 4 ∧ f' = f :=
  OmegaPilot.lieModel_POmega_two_unique_of_card_eq (Or.inr rfl) h8 h hcard

theorem lieModel_POmegaMinus_four_two_unique {X : Type} [Group X] {f f' : ℕ} {t : StatedLieTag}
    {n : ℕ} (h : LieModel X .POmegaMinus 4 2 f) (h' : LieModel X t n 2 f') :
    t = .POmegaMinus ∧ n = 4 ∧ f' = f :=
  lieModel_POmegaMinus_four_two_unique_of_card_eq h h' rfl

end Orders

end CFSG.SeitzReduction.TwistedE6Pilot
