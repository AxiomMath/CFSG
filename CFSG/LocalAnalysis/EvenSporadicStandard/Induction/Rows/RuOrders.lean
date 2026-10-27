module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuArith
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open

theorem statedClassicalModel_of_lieModel_ne_zero {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (hn : n ≠ 0) (h : LieModel X t n p f) : StatedClassicalModel X t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h

theorem dvd29_card_psp {X : Type} [Group X] {m : ℕ} (h : LieModel X .PSp 2 2 m) :
    29 ∣ Nat.card X ↔ 7 ∣ m := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (statedClassicalModel_of_lieModel_ne_zero (by norm_num) h)).2.2.1 rfl
  rw [hc]
  exact dvd29_ordBC_two m

theorem dvd29_card_psu_four {X : Type} [Group X] {m : ℕ} (h : LieModel X .PSU 4 2 m) :
    29 ∣ Nat.card X ↔ 7 ∣ m := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (statedClassicalModel_of_lieModel_ne_zero (by norm_num) h)).2.1 rfl
  rw [hc]
  exact dvd29_ordTwistedA (n := 3) (by norm_num) (by norm_num)

theorem dvd29_card_psu_five {X : Type} [Group X] {m : ℕ} (h : LieModel X .PSU 5 2 m) :
    29 ∣ Nat.card X ↔ 7 ∣ m := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (statedClassicalModel_of_lieModel_ne_zero (by norm_num) h)).2.1 rfl
  rw [hc]
  exact dvd29_ordTwistedA (n := 4) (by norm_num) (by norm_num)

theorem dvd29_card_psl_four {X : Type} [Group X] {m : ℕ} (h : LieModel X .PSL 4 2 m) :
    29 ∣ Nat.card X ↔ 7 ∣ m := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (statedClassicalModel_of_lieModel_ne_zero (by norm_num) h)).1 rfl
  rw [hc]
  exact dvd29_ordA (n := 3) (by norm_num) (by norm_num)

theorem dvd29_card_psl_five {X : Type} [Group X] {m : ℕ} (h : LieModel X .PSL 5 2 m) :
    29 ∣ Nat.card X ↔ 7 ∣ m := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (statedClassicalModel_of_lieModel_ne_zero (by norm_num) h)).1 rfl
  rw [hc]
  exact dvd29_ordA (n := 4) (by norm_num) (by norm_num)

end CFSG.EvenSporadicStandard.Induction
