module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Gen

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint

theorem sl2_card_mono {a b : ℕ} (h : a ≤ b) : a * (a ^ 2 - 1) ≤ b * (b ^ 2 - 1) := by
  apply Nat.mul_le_mul h
  apply Nat.sub_le_sub_right
  exact Nat.pow_le_pow_left h 2

theorem three_dvd_sl2_card (q : ℕ) : 3 ∣ q * (q ^ 2 - 1) := by
  have h : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases h with h | h | h
  · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _
  · refine Dvd.dvd.mul_left ?_ _
    have hq : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [← Nat.modEq_iff_dvd' hq]
    show 1 % 3 = q ^ 2 % 3
    rw [Nat.pow_mod, h]
  · refine Dvd.dvd.mul_left ?_ _
    have hq : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [← Nat.modEq_iff_dvd' hq]
    show 1 % 3 = q ^ 2 % 3
    rw [Nat.pow_mod, h]

theorem not_sl2_dvd_of_not_three {N : ℕ} (hN : ¬ 3 ∣ N) (q : ℕ) : ¬ q * (q ^ 2 - 1) ∣ N :=
  fun h => hN ((three_dvd_sl2_card q).trans h)

theorem not_sl2_dvd_of_bound {N B : ℕ} (hN0 : 0 < N) (hB : N < (B + 1) * ((B + 1) ^ 2 - 1))
    (hq : ∀ q, 5 ≤ q → q ≤ B → ¬ (q * (q ^ 2 - 1) ∣ N)) (q : ℕ) (hq5 : 5 ≤ q) :
    ¬ (q * (q ^ 2 - 1) ∣ N) := by
  intro hdvd
  by_cases hqB : q ≤ B
  · exact hq q hq5 hqB hdvd
  · have h1 := sl2_card_mono (show B + 1 ≤ q by omega)
    have h2 := Nat.le_of_dvd hN0 hdvd
    omega

theorem not_sl2_dvd_of_lt {N : ℕ} (hN0 : 0 < N) (hN : N < 120) (q : ℕ) (hq5 : 5 ≤ q) :
    ¬ (q * (q ^ 2 - 1) ∣ N) := by
  intro hdvd
  have h1 := sl2_card_mono hq5
  have h2 := Nat.le_of_dvd hN0 hdvd
  omega

theorem not_sl2_dvd_384 (q : ℕ) (hq5 : 5 ≤ q) : ¬ q * (q ^ 2 - 1) ∣ 384 :=
  not_sl2_dvd_of_bound (B := 7) (by norm_num) (by norm_num)
    (fun q h5 h7 => by interval_cases q <;> norm_num) q hq5

theorem not_sl2_dvd_192 (q : ℕ) (hq5 : 5 ≤ q) : ¬ q * (q ^ 2 - 1) ∣ 192 :=
  not_sl2_dvd_of_bound (B := 6) (by norm_num) (by norm_num)
    (fun q h5 h6 => by interval_cases q <;> norm_num) q hq5

theorem not_sl2_dvd_168 (q : ℕ) (hq5 : 5 ≤ q) : ¬ q * (q ^ 2 - 1) ∣ 168 :=
  not_sl2_dvd_of_bound (B := 6) (by norm_num) (by norm_num)
    (fun q h5 h6 => by interval_cases q <;> norm_num) q hq5

theorem sl2_card_ne_of_bound {N B : ℕ} (hB : N < (B + 1) * ((B + 1) ^ 2 - 1))
    (hq : ∀ q, 5 ≤ q → q ≤ B → q * (q ^ 2 - 1) ≠ N) (q : ℕ) (hq5 : 5 ≤ q) :
    q * (q ^ 2 - 1) ≠ N := by
  intro heq
  by_cases hqB : q ≤ B
  · exact hq q hq5 hqB heq
  · have h1 := sl2_card_mono (show B + 1 ≤ q by omega)
    omega

theorem sl2_card_ne_40320 (q : ℕ) (hq5 : 5 ≤ q) : q * (q ^ 2 - 1) ≠ 40320 :=
  sl2_card_ne_of_bound (B := 35) (by norm_num)
    (fun q h5 h35 => by interval_cases q <;> norm_num) q hq5

theorem sl2_card_ne_39916800 (q : ℕ) (hq5 : 5 ≤ q) : q * (q ^ 2 - 1) ≠ 39916800 :=
  sl2_card_ne_of_bound (B := 342) (by norm_num)
    (fun q h5 h342 => by revert q; decide +kernel) q hq5

theorem Ivk95Cfg.mul_self_eq_one {J : Type} [Group J] [Finite J] {z : J} (h : Ivk95Cfg z) :
    z * z = 1 := by
  rw [← pow_two, ← h.ord]
  exact pow_orderOf_eq_one z

theorem Ivk95Cfg.ne_one {J : Type} [Group J] [Finite J] {z : J} (h : Ivk95Cfg z) : z ≠ 1 := by
  intro h1
  have := h.ord
  rw [h1, orderOf_one] at this
  omega

namespace Ivk95Cfg

variable {J : Type} [Group J] [Finite J] {z : J}

theorem false_of_card_cent (h : Ivk95Cfg z)
    (hN : ∀ q : ℕ, 5 ≤ q → ¬ q * (q ^ 2 - 1) ∣ Nat.card ↥(centralizer ({z} : Set J))) : False := by
  obtain ⟨q, -, hq5, hKq⟩ := h.card_eq
  have hdvd : Nat.card ↥(Ez z) ∣ Nat.card ↥(centralizer ({z} : Set J)) :=
    Subgroup.card_dvd_of_le h.le_cent
  rw [hKq] at hdvd
  exact hN q hq5 hdvd

theorem false_of_card_cent_dvd (h : Ivk95Cfg z) {N : ℕ}
    (hC : Nat.card ↥(centralizer ({z} : Set J)) ∣ N)
    (hN : ∀ q : ℕ, 5 ≤ q → ¬ q * (q ^ 2 - 1) ∣ N) : False :=
  h.false_of_card_cent fun q hq hdvd => hN q hq (hdvd.trans hC)

theorem false_of_card_group (h : Ivk95Cfg z) {N : ℕ} (hJ : Nat.card J ∣ N)
    (hN : ∀ q : ℕ, 5 ≤ q → ¬ q * (q ^ 2 - 1) ∣ N) : False := by
  obtain ⟨q, -, hq5, hKq⟩ := h.card_eq
  have hdvd : Nat.card ↥(Ez z) ∣ Nat.card J := Subgroup.card_subgroup_dvd_card _
  rw [hKq] at hdvd
  exact hN q hq5 (hdvd.trans hJ)

end Ivk95Cfg

end CFSG.GH74.GLS.IVK.Proofs2
