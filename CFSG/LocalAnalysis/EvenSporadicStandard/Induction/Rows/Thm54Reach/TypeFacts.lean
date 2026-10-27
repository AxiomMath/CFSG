module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.OrderBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuReach
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar

public section

namespace CFSG.EvenSporadicStandard.Induction.Thm54Reach

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem evenLieType_of_thm54Types {X : Type} [Group X] (h : Sol78Thm54Types X) :
    EvenLieType X := by
  rcases h with ⟨n, hn, h⟩ | ⟨m, hm, h | h | h | h | h⟩
  · exact ⟨.twistedB2, 0, 2 * n + 1,
      LieModel.admissible (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩))),
      Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩))⟩
  · exact ⟨.PSp, 2, m, LieModel.admissible h, h⟩
  · exact ⟨.PSU, 4, m, LieModel.admissible h, h⟩
  · exact ⟨.PSL, 4, m, LieModel.admissible h, h⟩
  · exact ⟨.PSU, 5, m, LieModel.admissible h, h⟩
  · exact ⟨.PSL, 5, m, LieModel.admissible h, h⟩

theorem not_oddLieType_of_thm54Types (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : Sol78Thm54Types X) : ¬ OddLieType X := by
  rcases h with ⟨n, hn, h⟩ | ⟨m, hm, h | h | h | h | h⟩
  · exact CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two hO
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩)))
      (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide))
      (fun h => absurd h.1 (by decide))
  · exact CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two hO h
      (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide))
      (fun h => absurd h.1 (by decide))
  · exact CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two hO h
      (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide))
      (fun h => by have := h.2.2; omega)
  · exact CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two hO h
      (fun h => by have := h.2.1; omega) (fun h => by have := h.2.1; omega)
      (fun h => absurd h.1 (by decide))
  · exact CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two hO h
      (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide))
      (fun h => by have := h.2.1; omega)
  · exact CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two hO h
      (fun h => by have := h.2.1; omega) (fun h => by have := h.2.1; omega)
      (fun h => absurd h.1 (by decide))

theorem dvd29_card_suzuki' (hO : LieOrderFormulasInput) {X : Type} [Group X] {f : ℕ}
    (h : SuzukiModel X 2 f) : 29 ∣ Nat.card X ↔ 7 ∣ f := by
  have hcard := card_eq_of_suzukiModel hO h
  obtain ⟨-, a, ha, K, hKf, hKfin, hf, hK, ⟨e⟩⟩ := h
  subst hf
  rw [hcard]
  rw [show 2 ^ (2 * (2 * a + 1)) = (2 ^ (2 * a + 1)) ^ 2 by rw [← pow_mul]; ring]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    (dvd29_suzuki (f := 2 * a + 1) ⟨a, by ring⟩)

theorem lieFam_dvd29 {X : Type} [Group X] {m : ℕ} (h : LieFam X m) :
    29 ∣ Nat.card X ↔ 7 ∣ m := by
  rcases h with h | h | h | h | h
  · exact dvd29_card_psp h
  · exact dvd29_card_psu_four h
  · exact dvd29_card_psl_four h
  · exact dvd29_card_psu_five h
  · exact dvd29_card_psl_five h

theorem thm54_of_lieFam {X : Type} [Group X] {m : ℕ} (hm : 3 ≤ m) (h7 : ¬ 7 ∣ m)
    (h : LieFam X m) : Sol78Thm54Types X ∧ ¬ 29 ∣ Nat.card X := by
  exact ⟨Or.inr ⟨m, hm, h⟩, fun hd => h7 ((lieFam_dvd29 h).1 hd)⟩

end CFSG.EvenSporadicStandard.Induction.Thm54Reach
