module

public import CFSG.LocalAnalysis.OddStandard.SporadicRow.SixtyOrder
public import CFSG.Milestones.ASVolI.I2Covers

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup

theorem nonempty_mulEquiv_sl2_five_of_oddLieOrder
    {B : Type} [Group B] [Finite B] (hB : CFSG.IsQuasisimple B) {a : ℕ}
    (hd : Nat.card B ∣ 2 ^ a * 15) (hZ : center B ≠ ⊥)
    (hodd : OddLieOrder (Nat.card (B ⧸ center B))) :
    Nonempty (B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  have hq_dvd : Nat.card (B ⧸ center B) ∣ 2 ^ a * 15 :=
    (Subgroup.card_quotient_dvd_card (center B)).trans hd
  have h60 : Nat.card (B ⧸ center B) = 60 := hodd.eq_sixty_of_dvd hq_dvd
  have hBcard : Nat.card B = 60 * Nat.card (center B) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center B), h60]
  have hdz : 60 * Nat.card (center B) ∣ 2 ^ a * 15 := by
    rw [← hBcard]
    exact hd
  have h15 : 15 * (4 * Nat.card (center B)) ∣ 15 * 2 ^ a := by
    convert hdz using 1 <;> ring
  have h4 : 4 * Nat.card (center B) ∣ 2 ^ a :=
    (mul_dvd_mul_iff_left (show (15 : ℕ) ≠ 0 by norm_num)).1 h15
  have hz : Nat.card (center B) ∣ 2 ^ a :=
    (dvd_mul_left (Nat.card (center B)) 4).trans h4
  have h2 : IsPGroup 2 (center B) := IsPGroup.of_card_dvd_pow hz
  haveI : IsSimpleGroup (B ⧸ center B) := hB.2.1
  obtain ⟨e⟩ :=
    CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
      (G := B ⧸ center B) h60
  exact (CFSG.ASVolI.burnsideI2a_I_2_2_one hB hZ h2).1 ⟨e⟩

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
