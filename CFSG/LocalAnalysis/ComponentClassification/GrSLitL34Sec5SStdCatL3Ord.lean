module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdOrder
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Blueprint

theorem pow_dvd_card_of_lieModel_psl_three {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (hX : LieModel X .PSL 3 2 n) : 2 ^ (3 * n) ∣ Nat.card X := by
  rw [← padicValNat_card_of_lieModel_psl_three hn hX]
  exact pow_padicValNat_dvd

theorem dvd_card_of_lieModel_psl_three_even {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (hev : Even n) (hX : LieModel X .PSL 3 2 n) : 20160 ∣ Nat.card X := by
  rw [card_eq_of_lieModel_psl_three hX, ← pow_mul, ← pow_mul]
  have h2 : 2 ∣ n := even_iff_two_dvd.mp hev
  have h3 : Nat.gcd 3 (2 ^ n - 1) = 3 := Nat.gcd_eq_left (by
    simpa using Nat.pow_sub_one_dvd_pow_sub_one (x := 2) h2)
  obtain ⟨a, ha⟩ : 15 ∣ 2 ^ (n * 2) - 1 := by
    simpa using Nat.pow_sub_one_dvd_pow_sub_one (x := 2) (show 4 ∣ n * 2 by omega)
  obtain ⟨b, hb⟩ : 63 ∣ 2 ^ (n * 3) - 1 := by
    simpa using Nat.pow_sub_one_dvd_pow_sub_one (x := 2) (show 6 ∣ n * 3 by omega)
  obtain ⟨c, hc⟩ : 64 ∣ 2 ^ (n * 3) := by
    simpa using Nat.pow_dvd_pow 2 (show 6 ≤ n * 3 by omega)
  rw [h3, ha, hb, hc, show 64 * c * (15 * a * (63 * b)) = 3 * (20160 * (a * b * c)) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]
  exact dvd_mul_right _ _

theorem isComponent_and_lieModel_of_simple_psl_three {X : Type} [Group X] [Finite X]
    {P : Subgroup X} (hP : IsPComponent 2 P) [IsSimpleGroup P] {n : ℕ} (hn : 1 ≤ n)
    (hL : LieModel P .PSL 3 2 n) : IsComponent P ∧ LieModel (P ⧸ center P) .PSL 3 2 n := by
  have h4 : 4 ∣ Nat.card P := (show (4 : ℕ) ∣ 2 ^ (3 * n) from
    (Nat.pow_dvd_pow 2 (by omega : 2 ≤ 3 * n))).trans (pow_dvd_card_of_lieModel_psl_three hn hL)
  have hna : ∃ a b : P, a * b ≠ b * a := L34PF.nonabelian_of_simple_of_four_dvd h4
  have hZ : center P = ⊥ := CatLeaf.center_eq_bot_of_simple hna
  exact ⟨⟨L34PF.isQuasisimple_of_simple hna, hP.choose_spec.2.1⟩,
    LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hL⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S
