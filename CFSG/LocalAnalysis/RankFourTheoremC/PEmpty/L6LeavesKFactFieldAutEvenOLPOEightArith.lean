module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLThreeArith
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)

namespace OLEight

theorem two_pow_mod_27 (n : ℕ) : 2 ^ n % 27 = 2 ^ (n % 18) % 27 := by
  conv_lhs => rw [← Nat.div_add_mod n 18, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem two_pow_six_mul_mod_27 {p : ℕ} (hp : p % 6 = 1 ∨ p % 6 = 5) :
    2 ^ (p * 6) % 27 = 10 ∨ 2 ^ (p * 6) % 27 = 19 := by
  rw [two_pow_mod_27]
  have h : (p * 6) % 18 = 6 ∨ (p * 6) % 18 = 12 := by omega
  rcases h with h | h <;> rw [h] <;> norm_num

theorem padicValNat_three_sub_one_two {X : ℕ} (hX : 1 ≤ X) (h : X % 27 = 10 ∨ X % 27 = 19) :
    padicValNat 3 (X - 1) = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : X - 1 ≠ 0 := by omega
  have h1 : 2 ≤ padicValNat 3 (X - 1) :=
    (padicValNat_dvd_iff_le hne).mp (by norm_num; omega)
  have h2 : ¬ 3 ≤ padicValNat 3 (X - 1) := fun h2 => by
    have := (padicValNat_dvd_iff_le hne).mpr h2
    norm_num at this
    omega
  omega

theorem padicValNat_three_two_pow_six_sub_one {p : ℕ} (hp : p % 6 = 1 ∨ p % 6 = 5) :
    padicValNat 3 (2 ^ (p * 6) - 1) = 2 :=
  padicValNat_three_sub_one_two Nat.one_le_two_pow (two_pow_six_mul_mod_27 hp)

theorem padicValNat_three_two_pow_mul_sub_one_le_six {p k : ℕ} (hp : p % 6 = 1 ∨ p % 6 = 5)
    (hk1 : 1 ≤ k) (hk6 : k ≤ 6) :
    padicValNat 3 (2 ^ (p * k) - 1) = if k = 6 then 2 else (k + 1) % 2 := by
  rcases Nat.lt_or_ge k 6 with h | h
  · rw [if_neg (by omega)]
    exact OLThreeAdic.padicValNat_three_two_pow_mul_sub_one hp hk1 (by omega)
  · have hk : k = 6 := by omega
    subst hk
    rw [if_pos rfl]
    exact padicValNat_three_two_pow_six_sub_one hp

theorem padicValNat_three_prod_gl_le_six {p : ℕ} (hp : p % 6 = 1 ∨ p % 6 = 5) {a : ℕ}
    (ha : a ≤ 6) :
    padicValNat 3 (∏ i : Fin a, ((2 ^ p) ^ a - (2 ^ p) ^ (i : ℕ))) =
      if a = 6 then 4 else a / 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp1 : 1 ≤ p := by omega
  have hfac : ∀ i : Fin a, (2 ^ p) ^ a - (2 ^ p) ^ (i : ℕ) =
      2 ^ (p * (i : ℕ)) * (2 ^ (p * (a - i)) - 1) := fun i => by
    have hi : (i : ℕ) ≤ a := i.2.le
    have e1 : (2 ^ p) ^ a = 2 ^ (p * (i : ℕ)) * 2 ^ (p * (a - i)) := by
      rw [← pow_add, ← mul_add, Nat.add_sub_cancel' hi, pow_mul]
    rw [e1, Nat.mul_sub_one, pow_mul]
  have hne1 : ∀ i : Fin a, 2 ^ (p * (a - i)) - 1 ≠ 0 := fun i => by
    have hi : 1 ≤ a - (i : ℕ) := by have := i.2; omega
    have := OLThreeAdic.two_le_two_pow_mul hp1 hi
    omega
  simp only [hfac]
  rw [OLThreeAdic.padicValNat_three_prod _ _
    (fun i _ => mul_ne_zero (pow_ne_zero _ two_ne_zero) (hne1 i))]
  have hterm : ∀ i : Fin a, padicValNat 3 (2 ^ (p * (i : ℕ)) * (2 ^ (p * (a - i)) - 1)) =
      if a - (i : ℕ) = 6 then 2 else (a - (i : ℕ) + 1) % 2 := fun i => by
    have hi1 : 1 ≤ a - (i : ℕ) := by have := i.2; omega
    have hi6 : a - (i : ℕ) ≤ 6 := by omega
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) (hne1 i),
      padicValNat.eq_zero_of_not_dvd (OLThreeAdic.not_three_dvd_two_pow _), zero_add,
      padicValNat_three_two_pow_mul_sub_one_le_six hp hi1 hi6]
  simp only [hterm]
  interval_cases a <;> simp [Fin.sum_univ_succ]

section Card

variable {F : Type*} [Field F] [Finite F]

theorem natCard_GL (a : ℕ) :
    Nat.card (GL (Fin a) F) = ∏ i : Fin a, (Nat.card F ^ a - Nat.card F ^ (i : ℕ)) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_GL_field, Nat.card_eq_fintype_card (α := F)]

theorem padicValNat_three_card_GL_le_six {p : ℕ} (hq : Nat.card F = 2 ^ p)
    (hp : p % 6 = 1 ∨ p % 6 = 5) {a : ℕ} (ha : a ≤ 6) :
    padicValNat 3 (Nat.card (GL (Fin a) F)) = if a = 6 then 4 else a / 2 := by
  rw [natCard_GL, hq]
  exact padicValNat_three_prod_gl_le_six hp ha

theorem levi_bound_eight {p : ℕ} (hq : Nat.card F = 2 ^ p) (hp : p % 6 = 1 ∨ p % 6 = 5) :
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ 8 →
      padicValNat 3 (Nat.card (GL (Fin k) F)) +
        padicValNat 3 (Nat.card (GL (Fin (8 - 2 * k)) F)) ≤ 4 := by
  intro k hk1 hk2
  have h1 := padicValNat_three_card_GL_le_six hq hp (a := k) (by omega)
  have h2 := padicValNat_three_card_GL_le_six hq hp (a := 8 - 2 * k) (by omega)
  rw [h1, h2]
  split_ifs <;> omega

end Card

theorem lieOrderDivisor_POmegaPlus_four : lieOrderDivisor .POmegaPlus 4 (2 ^ 1) = 1 := by
  decide

theorem five_le_padicValNat_numerator_POmegaPlus_four :
    5 ≤ padicValNat 3 (lieOrderNumerator .POmegaPlus 4 (2 ^ 1)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : lieOrderNumerator .POmegaPlus 4 (2 ^ 1) = 2 ^ 12 * 15 * (3 * 15 * 63) := by decide
  have hne : lieOrderNumerator .POmegaPlus 4 (2 ^ 1) ≠ 0 := by rw [h]; norm_num
  exact (padicValNat_dvd_iff_le hne).mp (by rw [h]; norm_num)

end OLEight

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
