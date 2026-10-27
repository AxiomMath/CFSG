module

public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PerfectCover.HopfCover
import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.Quasithin.B69K.OddCovers

open CFSG.RankThree.PerfectCover CFSG.Blueprint.Multiplier CFSG.Open

theorem lieModel_of_stated {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel X t n p f) : CFSG.Models.LieModel X t n p f :=
  ⟨h.1, Or.inl h⟩

theorem card_hopfMultiplier_table (hGA : GriessAllModelsStatement) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hM : CFSG.Models.LieModel X t n p f) :
    Nat.card (hopfMultiplier X) =
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨e⟩⟩ := hGA X t n p f hM
  rw [← Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv, Nat.card_congr e.toEquiv]
  simp only [generic, exceptional, Nat.card_prod,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod _) ≃ _), Nat.card_zmod]

theorem card_hopfMultiplier_psl2 (hGA : GriessAllModelsStatement) {X : Type} [Group X] {f : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 f) : Nat.card (hopfMultiplier X) ∣ 4 := by
  have hcard := card_hopfMultiplier_table hGA (lieModel_of_stated h)
  have hgen : genericOrders .PSL 2 2 f = (Nat.gcd 2 (2 ^ f - 1), 1) := rfl
  have hexc : (exceptionalOrders .PSL 2 2 f).1 * (exceptionalOrders .PSL 2 2 f).2 ∣ 2 := by
    unfold exceptionalOrders
    split <;> first | omega | contradiction | norm_num
  have hg : Nat.gcd 2 (2 ^ f - 1) * 1 ∣ 2 := by
    rw [mul_one]
    exact Nat.gcd_dvd_left 2 (2 ^ f - 1)
  rw [hcard, hgen]
  exact Nat.dvd_trans (mul_dvd_mul hg hexc) (by norm_num)

theorem card_hopfMultiplier_psp2 (hGA : GriessAllModelsStatement) {X : Type} [Group X] {f : ℕ}
    (h : StatedClassicalModel X .PSp 2 2 f) : Nat.card (hopfMultiplier X) ∣ 2 := by
  have hcard := card_hopfMultiplier_table hGA (lieModel_of_stated h)
  have hgen : genericOrders .PSp 2 2 f = (Nat.gcd 2 (2 ^ f - 1), 1) := rfl
  have hexc : (exceptionalOrders .PSp 2 2 f).1 * (exceptionalOrders .PSp 2 2 f).2 ∣ 1 := by
    unfold exceptionalOrders
    split <;> first | omega | contradiction | norm_num
  have hg : Nat.gcd 2 (2 ^ f - 1) * 1 ∣ 2 := by
    rw [mul_one]
    exact Nat.gcd_dvd_left 2 (2 ^ f - 1)
  rw [hcard, hgen]
  exact Nat.dvd_trans (mul_dvd_mul hg hexc) (by norm_num)

theorem card_hopfMultiplier_psl3 (hGA : GriessAllModelsStatement) {X : Type} [Group X] {f : ℕ}
    (h : StatedClassicalModel X .PSL 3 2 f) :
    ∃ m : ℕ, m ∣ 16 ∧ Nat.card (hopfMultiplier X) = Nat.gcd 3 (2 ^ f - 1) * m := by
  have hcard := card_hopfMultiplier_table hGA (lieModel_of_stated h)
  have hgen : genericOrders .PSL 3 2 f = (Nat.gcd 3 (2 ^ f - 1), 1) := rfl
  refine ⟨(exceptionalOrders .PSL 3 2 f).1 * (exceptionalOrders .PSL 3 2 f).2, ?_, ?_⟩
  · unfold exceptionalOrders
    split <;> first | omega | contradiction | norm_num
  · rw [hcard, hgen]
    simp

theorem card_hopfMultiplier_psu3 (hGA : GriessAllModelsStatement) {X : Type} [Group X] {f : ℕ}
    (h : StatedClassicalModel X .PSU 3 2 f) :
    Nat.card (hopfMultiplier X) = Nat.gcd 3 (2 ^ f + 1) := by
  have hcard := card_hopfMultiplier_table hGA (lieModel_of_stated h)
  have hgen : genericOrders .PSU 3 2 f = (Nat.gcd 3 (2 ^ f + 1), 1) := rfl
  have hexc : (exceptionalOrders .PSU 3 2 f).1 * (exceptionalOrders .PSU 3 2 f).2 = 1 := by
    unfold exceptionalOrders
    split <;> first | omega | contradiction | norm_num
  rw [hcard, hgen, hexc]
  simp

end CFSG.Quasithin.B69K.OddCovers

end
