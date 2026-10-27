module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitStd

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def Sol78Thm24_1CIT : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N : Subgroup H), FStarSimple N → ∀ A : Subgroup H, SolStd A →
    (∃ S : Sylow 2 (centralizer (A : Set H)), IsGenQuaternion ↥S) →
      OddLieType ↥N ∨ IsSporadic ↥N .M11 ∨ IsSporadic ↥N .M12

@[expose] def Sol78Thm24_1Use : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N : Subgroup H), FStarSimple N → ¬ Nat.card ↥N ∣ 95040 →
    ∀ A : Subgroup H, SolStd A →
      (∃ S : Sylow 2 (centralizer (A : Set H)), IsGenQuaternion ↥S) → OddLieType ↥N

theorem not_dvd_95040_of_seven_dvd {n : ℕ} (h : 7 ∣ n) : ¬ n ∣ 95040 :=
  fun hn => by have := h.trans hn; omega

theorem not_dvd_95040_of_lt {n : ℕ} (h : 95040 < n) : ¬ n ∣ 95040 :=
  fun hn => by have := Nat.le_of_dvd (by norm_num) hn; omega

theorem not_card_dvd_95040_of_le_of_seven_dvd {H : Type} [Group H] [Finite H] {A N : Subgroup H}
    (hAN : A ≤ N) (h7 : 7 ∣ Nat.card ↥A) : ¬ Nat.card ↥N ∣ 95040 :=
  not_dvd_95040_of_seven_dvd (h7.trans (Subgroup.card_dvd_of_le hAN))

theorem not_card_dvd_95040_of_le_of_lt {H : Type} [Group H] [Finite H] {A N : Subgroup H}
    (hAN : A ≤ N) (h : 95040 < Nat.card ↥A) : ¬ Nat.card ↥N ∣ 95040 :=
  not_dvd_95040_of_lt
    (h.trans_le (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hAN)))

theorem not_card_top_dvd_95040_of_seven_dvd {G : Type} [Group G] (h : 7 ∣ Nat.card G) :
    ¬ Nat.card ↥(⊤ : Subgroup G) ∣ 95040 := by
  rw [Subgroup.card_top]
  exact not_dvd_95040_of_seven_dvd h

theorem not_card_top_dvd_95040_of_hs_dvd {G : Type} [Group G] (h : 44352000 ∣ Nat.card G) :
    ¬ Nat.card ↥(⊤ : Subgroup G) ∣ 95040 :=
  not_card_top_dvd_95040_of_seven_dvd ((show 7 ∣ 44352000 by norm_num).trans h)

end CFSG.EvenSporadicStandard.Induction
