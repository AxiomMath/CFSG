module

public import CFSG.Monster.Existence.Defs
public import CFSG.Sporadic.Co2
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.HN
public import CFSG.LargeExtraspecial.A2ModOrdCard

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup CFSG.Blueprint CFSG.Monster.Existence CFSG.LargeExtraspecial.A2Mod.Ord CFSG.Open

section Shapes

variable {G : Type} [Group G]


theorem nineteen_dvd_of_twoPointShape_one {H : Subgroup G} (h : TwoPointShape H 1) :
    19 ∣ Nat.card H := by
  simp only [TwoPointShape] at h
  obtain ⟨N, hN, -, hN4, hX⟩ := h
  have h1 : Nat.card H = Nat.card (H ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [h1, card_of_lieModel_twistedE6 hX, hN4]
  norm_num [ordTwistedE6]

section Certified

theorem not_dvd_thirteen_of_twoPointShape {H : Subgroup G} {i : Fin 9}
    (hi : i = 2 ∨ i = 5 ∨ i = 7) (h : TwoPointShape H i) : ¬ 13 ∣ Nat.card H := by
  rcases hi with rfl | rfl | rfl
  · simp only [TwoPointShape, HasLayeredTwoShape] at h
    obtain ⟨N, hN, N₀, hN₀, -, -, -, -, hNc, ⟨e⟩⟩ := h
    have h1 : Nat.card H = Nat.card (H ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [h1, Nat.card_congr e.toEquiv, CFSG.Sporadic.Co2.card_Co2, hNc]
    norm_num
  · simp only [TwoPointShape] at h
    obtain ⟨N, hN, -, hN23, ⟨e⟩⟩ := h
    have h1 : Nat.card H = Nat.card (H ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [h1, Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL, hN23]
    norm_num
  · simp only [TwoPointShape] at h
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.HN.card_HN]
    norm_num

end Certified

end Shapes

end CFSG.HardMathSupport.Dickson.Sec6.I1431
