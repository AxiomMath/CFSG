module

public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem factorization_two_of_mul_eq {a g k m : ℕ} (hg : ¬ 2 ∣ g) (hm : ¬ 2 ∣ m) (ha : a ≠ 0)
    (h : a * g = 2 ^ k * m) : a.factorization 2 = k := by
  have hg0 : g ≠ 0 := fun h0 => hg (h0 ▸ dvd_zero 2)
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero 2)
  have h1 := congrArg (fun x => x.factorization 2) h
  rw [Nat.factorization_mul ha hg0, Nat.factorization_mul (by positivity) hm0,
    Nat.Prime.factorization_pow Nat.prime_two] at h1
  simp [Nat.factorization_eq_zero_of_not_dvd hg, Nat.factorization_eq_zero_of_not_dvd hm] at h1
  exact h1

theorem odd_pred_of_even {x : ℕ} (hx : Even x) (h0 : 0 < x) : Odd (x - 1) := by
  obtain ⟨c, rfl⟩ := hx
  exact ⟨c - 1, by omega⟩

theorem odd_pow_sub_one_of_even {q k : ℕ} (hq : Even q) (hq0 : 0 < q) (hk : k ≠ 0) :
    Odd (q ^ k - 1) :=
  odd_pred_of_even (hq.pow_of_ne_zero hk) (pow_pos hq0 k)

theorem odd_pow_add_one_of_even {q k : ℕ} (hq : Even q) (hk : k ≠ 0) : Odd (q ^ k + 1) :=
  (hq.pow_of_ne_zero hk).add_one

theorem two_pow_even {n : ℕ} (hn : 1 ≤ n) : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩

theorem not_two_dvd_of_odd {m : ℕ} (h : Odd m) : ¬ 2 ∣ m := fun hd =>
  (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr hd)

theorem factorization_two_card_Suzuki {G : Type} [Group G]
    [Finite G] {n : ℕ} (h : CFSG.Blueprint.SuzukiModel G 2 n) : (Nat.card G).factorization 2 = 2 * n ∧ Odd n := by
  obtain ⟨-, a, ha, hn, hcard⟩ := CFSG.GH74.card_of_suzukiModel h
  have hn1 : 1 ≤ n := by omega
  have hq0 : 0 < 2 ^ n := pow_pos (by norm_num) n
  have hqe : Even (2 ^ n) := two_pow_even hn1
  refine ⟨?_, ⟨a, by omega⟩⟩
  have hodd : ¬ 2 ∣ ((2 ^ n) ^ 2 + 1) * (2 ^ n - 1) :=
    not_two_dvd_of_odd ((odd_pow_add_one_of_even hqe (by norm_num)).mul
      (by simpa using odd_pow_sub_one_of_even hqe hq0 (k := 1) one_ne_zero))
  have hne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  refine factorization_two_of_mul_eq (g := 1) (by norm_num) hodd hne ?_
  rw [hn] at hcard
  rw [hcard, mul_one, ordSuzuki, ← hn, mul_assoc, ← pow_mul, mul_comm n 2]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
