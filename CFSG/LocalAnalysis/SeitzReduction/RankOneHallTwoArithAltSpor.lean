module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.Nat.Multiplicity

public section

namespace CFSG.SeitzReduction.RankOne

open scoped Nat

@[expose] def HallTwoArith (c : ℕ) : Prop :=
  ∃ e h, 1 ≤ e ∧ c = 2 ^ e * h ∧ Odd h ∧ h ∣ (2 ^ e - 1) * e

theorem le_of_two_pow_mul_eq_two_pow_mul_odd {a b x y : ℕ} (hy : Odd y)
    (h : 2 ^ a * x = 2 ^ b * y) : a ≤ b := by
  by_contra hlt
  have h1 : 2 ^ (b + 1) ∣ 2 ^ b * y := h ▸ (pow_dvd_pow 2 (by omega)).mul_right x
  rw [pow_succ] at h1
  have h2 := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ b)).mp h1
  exact (Nat.not_even_iff_odd.mpr hy) (even_iff_two_dvd.mpr h2)

theorem two_pow_mul_odd_inj {e e' h h' : ℕ} (hh : Odd h) (hh' : Odd h')
    (heq : 2 ^ e * h = 2 ^ e' * h') : e = e' ∧ h = h' := by
  obtain rfl : e = e' := le_antisymm (le_of_two_pow_mul_eq_two_pow_mul_odd hh' heq)
    (le_of_two_pow_mul_eq_two_pow_mul_odd hh heq.symm)
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) heq⟩

theorem hallTwoArith_iff {c e h : ℕ} (hc : c = 2 ^ e * h) (hh : Odd h) :
    HallTwoArith c ↔ 1 ≤ e ∧ h ∣ (2 ^ e - 1) * e := by
  constructor
  · rintro ⟨e', h', he', hc', hh', hdiv⟩
    obtain ⟨rfl, rfl⟩ := two_pow_mul_odd_inj hh hh' (hc.symm.trans hc')
    exact ⟨he', hdiv⟩
  · rintro ⟨he, hdiv⟩
    exact ⟨e, h, he, hc, hh, hdiv⟩

theorem not_hallTwoArith_of_eq {c e h : ℕ} (hc : c = 2 ^ e * h) (hh : Odd h)
    (hnd : ¬ h ∣ (2 ^ e - 1) * e) : ¬ HallTwoArith c :=
  fun H => hnd ((hallTwoArith_iff hc hh).1 H).2

theorem not_hallTwoArith_card_of_mulEquiv {T S : Type*} [Group T] [Group S] (θ : T ≃* S)
    {e h : ℕ} (hS : Nat.card S = 2 ^ e * h) (hh : Odd h) (hnd : ¬ h ∣ (2 ^ e - 1) * e) :
    ¬ HallTwoArith (Nat.card T) :=
  not_hallTwoArith_of_eq ((Nat.card_congr θ.toEquiv).trans hS) hh hnd

theorem lt_of_dvd_two_pow_sub_one_mul {c e h : ℕ} (he : 1 ≤ e) (hc : c = 2 ^ e * h)
    (hdiv : h ∣ (2 ^ e - 1) * e) : c < 2 ^ (2 * e) * e := by
  have h2 : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hpos : 0 < (2 ^ e - 1) * e := Nat.mul_pos (by omega) (by omega)
  have hle : h ≤ (2 ^ e - 1) * e := Nat.le_of_dvd hpos hdiv
  calc c = 2 ^ e * h := hc
    _ ≤ 2 ^ e * ((2 ^ e - 1) * e) := Nat.mul_le_mul_left _ hle
    _ < 2 ^ e * (2 ^ e * e) := by
        apply Nat.mul_lt_mul_of_pos_left _ (by positivity)
        exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    _ = 2 ^ (2 * e) * e := by ring

theorem two_pow_mul_le_factorial_add_nine (j : ℕ) : 2 ^ (2 * j + 15) * (j + 7) ≤ (j + 9)! := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [show j + 1 + 9 = (j + 9) + 1 by ring, Nat.factorial_succ]
    calc 2 ^ (2 * (j + 1) + 15) * (j + 1 + 7) = 4 * (j + 8) * 2 ^ (2 * j + 15) := by ring
      _ ≤ (j + 9 + 1) * (j + 7) * 2 ^ (2 * j + 15) := by
          apply Nat.mul_le_mul_right
          nlinarith
      _ = (j + 9 + 1) * (2 ^ (2 * j + 15) * (j + 7)) := by ring
      _ ≤ (j + 9 + 1) * (j + 9)! := Nat.mul_le_mul_left _ ih

theorem not_hallTwoArith_alternating {k : ℕ} (hk : 5 ≤ k) : ¬ HallTwoArith (k ! / 2) := by
  rcases (by omega : k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ 9 ≤ k) with rfl | rfl | rfl | rfl | h9
  · exact not_hallTwoArith_of_eq (e := 2) (h := 15) (by decide) (by decide) (by decide)
  · exact not_hallTwoArith_of_eq (e := 3) (h := 45) (by decide) (by decide) (by decide)
  · exact not_hallTwoArith_of_eq (e := 3) (h := 315) (by decide) (by decide) (by decide)
  · exact not_hallTwoArith_of_eq (e := 6) (h := 315) (by decide) (by decide) (by decide)
  · rintro ⟨e, h, he1, hc, hh, hdiv⟩
    have h2 : 2 ∣ k ! := Nat.dvd_factorial (by norm_num) (by omega)
    have hk! : k ! = 2 ^ (e + 1) * h := by
      rw [← Nat.mul_div_cancel' h2, hc]
      ring
    have hlt : e + 1 < k := by
      have h1 := Nat.emultiplicity_two_factorial_lt (show k ≠ 0 by omega)
      have h2 := le_emultiplicity_of_pow_dvd (hk! ▸ dvd_mul_right (2 ^ (e + 1)) h)
      exact_mod_cast lt_of_le_of_lt h2 h1
    have hbound := lt_of_dvd_two_pow_sub_one_mul he1 hc hdiv
    have hk2 : k ! < 2 ^ (2 * e + 1) * e := by
      rw [← Nat.mul_div_cancel' h2]
      calc 2 * (k ! / 2) < 2 * (2 ^ (2 * e) * e) := by omega
        _ = 2 ^ (2 * e + 1) * e := by ring
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 9 := ⟨k - 9, by omega⟩
    have hle : 2 ^ (2 * e + 1) * e ≤ 2 ^ (2 * j + 15) * (j + 7) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) (by omega)
    have := two_pow_mul_le_factorial_add_nine j
    omega

theorem not_hallTwoArith_card_of_mulEquiv_alternatingGroup {T : Type*} [Group T] {k : ℕ}
    (hk : 5 ≤ k) (θ : T ≃* alternatingGroup (Fin k)) : ¬ HallTwoArith (Nat.card T) := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  exact not_hallTwoArith_alternating hk

end CFSG.SeitzReduction.RankOne
