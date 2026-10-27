module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Defs

public section

namespace CFSG.OddStandard.Seitz77

open Matrix

theorem card_GL8_two :
    Nat.card (GL (Fin 8) (ZMod 2)) = 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_eight]
  norm_num

theorem factorization_GL8_apply (p : ℕ) :
    (2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 : ℕ).factorization p =
      28 * (if 2 = p then 1 else 0) + 5 * (if 3 = p then 1 else 0) +
        2 * (if 5 = p then 1 else 0) + 2 * (if 7 = p then 1 else 0) +
        (if 17 = p then 1 else 0) + (if 31 = p then 1 else 0) +
        (if 127 = p then 1 else 0) := by
  have h2 : Nat.Prime 2 := by norm_num
  have h3 : Nat.Prime 3 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have h17 : Nat.Prime 17 := by norm_num
  have h31 : Nat.Prime 31 := by norm_num
  have h127 : Nat.Prime 127 := by norm_num
  rw [Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, h2.factorization,
    h3.factorization, h5.factorization, h7.factorization, h17.factorization, h31.factorization,
    h127.factorization, Finsupp.single_apply, smul_eq_mul]

theorem prime_dvd_GL8 {p : ℕ} (hp : p.Prime)
    (h : p ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 ∨ p = 31 ∨ p = 127 := by
  have hne : (2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 : ℕ) ≠ 0 := by norm_num
  have h0 : 0 < (2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 : ℕ).factorization p :=
    (hp.factorization_pos_of_dvd hne h)
  rw [factorization_GL8_apply] at h0
  split_ifs at h0 <;> omega

theorem factorization_GL8_le_five {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    (2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 : ℕ).factorization p ≤ 5 := by
  have _ := hp
  rw [factorization_GL8_apply]
  split_ifs <;> omega

theorem eq_two_or_three_of_three_le {p : ℕ} (hp : p.Prime)
    (h : 3 ≤ (2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 : ℕ).factorization p) :
    p = 2 ∨ p = 3 := by
  have _ := hp
  rw [factorization_GL8_apply] at h
  split_ifs at h <;> omega

theorem factorization_GL8_three :
    (2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 : ℕ).factorization 3 = 5 := by
  rw [factorization_GL8_apply]
  norm_num

theorem factorization_le_GL8 {n : ℕ} (hn : n ≠ 0)
    (h : n ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127) (p : ℕ) :
    n.factorization p ≤ (2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 : ℕ).factorization p :=
  (Nat.factorization_le_iff_dvd hn (by norm_num)).2 h p

theorem not_le_factorization_GL8_of_six_le {p k f : ℕ} (hp : p.Prime) (h2 : p ≠ 2)
    (hf : 1 ≤ f) (hk : 6 ≤ k) :
    ¬ k * f ≤ (2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 : ℕ).factorization p := by
  intro h
  have := factorization_GL8_le_five hp h2
  nlinarith

theorem eq_three_of_four_mul_le {p f : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hf : 1 ≤ f)
    (h : 4 * f ≤ (2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 : ℕ).factorization p) :
    p = 3 ∧ f = 1 := by
  have h5 := factorization_GL8_le_five hp h2
  have hp3 : p = 3 := by
    rcases eq_two_or_three_of_three_le hp (by omega) with h' | h'
    · exact absurd h' h2
    · exact h'
  subst hp3
  exact ⟨rfl, by omega⟩

theorem eq_three_of_three_mul_le {p f : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hf : 1 ≤ f)
    (h : 3 * f ≤ (2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 : ℕ).factorization p) :
    p = 3 ∧ f = 1 := by
  have h5 := factorization_GL8_le_five hp h2
  have hp3 : p = 3 := by
    rcases eq_two_or_three_of_three_le hp (by omega) with h' | h'
    · exact absurd h' h2
    · exact h'
  subst hp3
  exact ⟨rfl, by omega⟩

theorem not_dvd_GL8_of_prime {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (h3 : q ≠ 3) (h5 : q ≠ 5)
    (h7 : q ≠ 7) (h17 : q ≠ 17) (h31 : q ≠ 31) (h127 : q ≠ 127) :
    ¬ q ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 := by
  intro h
  rcases prime_dvd_GL8 hq h with h | h | h | h | h | h | h <;> contradiction

theorem not_dvd_GL8_eleven : ¬ 11 ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 :=
  not_dvd_GL8_of_prime (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_dvd_GL8_thirteen : ¬ 13 ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 :=
  not_dvd_GL8_of_prime (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_dvd_GL8_nineteen : ¬ 19 ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 :=
  not_dvd_GL8_of_prime (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem Mod27.card_dvd {N : Type} [Group N] [Finite N] {X : Subgroup N} (m : Mod27 N X) :
    Nat.card N ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 := by
  obtain ⟨H, _, _, ρ, π, hρ, hπ, -, -⟩ := m.exists_module
  rw [← card_GL8_two]
  exact (Subgroup.card_dvd_of_surjective hπ).trans (Subgroup.card_dvd_of_injective ρ hρ)

end CFSG.OddStandard.Seitz77
