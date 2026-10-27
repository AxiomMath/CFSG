module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.GH74.GLS.Stage4.Q9

theorem numerics_two_pow_four_dvd (d : ℕ) (hd : d ≠ 0) (h : 2 ^ 7 ∣ d ^ 2) : 2 ^ 4 ∣ d := by
  have hp : Nat.Prime 2 := Nat.prime_two
  rw [hp.pow_dvd_iff_le_factorization (pow_ne_zero 2 hd), Nat.factorization_pow] at h
  rw [hp.pow_dvd_iff_le_factorization hd]
  simp at h
  omega

theorem numerics_three_sq_dvd (d : ℕ) (hd : d ≠ 0) (h : 3 ^ 4 ∣ d ^ 2) : 3 ^ 2 ∣ d := by
  have hp : Nat.Prime 3 := Nat.prime_three
  rw [hp.pow_dvd_iff_le_factorization (pow_ne_zero 2 hd), Nat.factorization_pow] at h
  rw [hp.pow_dvd_iff_le_factorization hd]
  simp at h
  omega

theorem numerics_dvd_720 (F x d : ℕ) (hFN : F * d ^ 2 = 43571520 * (x * (x + 1)))
    (hcop : Nat.Coprime F 30) (hd0 : 0 < d) : 720 ∣ d := by
  have hc2 : Nat.Coprime F 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hcop
  have hc3 : Nat.Coprime F 3 := Nat.Coprime.coprime_dvd_right (by norm_num) hcop
  have hc5 : Nat.Coprime F 5 := Nat.Coprime.coprime_dvd_right (by norm_num) hcop
  have h2 : 2 ^ 7 ∣ d ^ 2 := by
    have h : 2 ^ 7 ∣ F * d ^ 2 := by
      rw [hFN]
      obtain ⟨k, hk⟩ := Nat.even_mul_succ_self x
      rw [hk]
      exact ⟨680805 * k, by ring⟩
    exact (Nat.Coprime.pow_left 7 hc2.symm).dvd_of_dvd_mul_left h
  have h3 : 3 ^ 4 ∣ d ^ 2 := by
    have h : 3 ^ 4 ∣ F * d ^ 2 := by
      rw [hFN]
      exact Dvd.dvd.mul_right ⟨537920, by norm_num⟩ _
    exact (Nat.Coprime.pow_left 4 hc3.symm).dvd_of_dvd_mul_left h
  have h5 : 5 ∣ d := by
    have h : 5 ∣ F * d ^ 2 := by
      rw [hFN]
      exact Dvd.dvd.mul_right ⟨8714304, by norm_num⟩ _
    exact Nat.prime_five.dvd_of_dvd_pow (hc5.symm.dvd_of_dvd_mul_left h)
  have d16 := numerics_two_pow_four_dvd d hd0.ne' h2
  have d9 := numerics_three_sq_dvd d hd0.ne' h3
  omega

theorem numerics_lower_bound_Z (F D X : ℤ) (hD : 29520 ≤ D) (hX : D - 509 ≤ X)
    (hF : F * D ^ 2 = 43571520 * X * (X + 1)) : 81 * 518400 < F := by
  by_contra hlow
  have hlow := not_lt.mp hlow
  obtain ⟨e, he, rfl⟩ : ∃ e : ℤ, 0 ≤ e ∧ D = 29520 + e := ⟨D - 29520, by omega, by ring⟩
  obtain ⟨u, hu, rfl⟩ : ∃ u : ℤ, 0 ≤ u ∧ X = 29011 + e + u :=
    ⟨X - (29011 + e), by omega, by ring⟩
  have h1 : F * (29520 + e) ^ 2 ≤ 81 * 518400 * (29520 + e) ^ 2 :=
    mul_le_mul_of_nonneg_right hlow (sq_nonneg _)
  nlinarith [mul_nonneg he hu, mul_nonneg he he, mul_nonneg hu hu]

theorem numerics_upper_bound_Z (F D X : ℤ) (hD : 29520 ≤ D) (hX0 : 0 ≤ X) (hX : X ≤ D + 509)
    (hF : F * D ^ 2 = 43571520 * X * (X + 1)) : F < 88 * 518400 := by
  by_contra hup
  have hup := not_lt.mp hup
  obtain ⟨e, he, rfl⟩ : ∃ e : ℤ, 0 ≤ e ∧ D = 29520 + e := ⟨D - 29520, by omega, by ring⟩
  obtain ⟨w, hw, rfl⟩ : ∃ w : ℤ, 0 ≤ w ∧ X = 30029 + e - w :=
    ⟨30029 + e - X, by omega, by ring⟩
  have h1 : 88 * 518400 * (29520 + e) ^ 2 ≤ F * (29520 + e) ^ 2 :=
    mul_le_mul_of_nonneg_right hup (sq_nonneg _)
  nlinarith [mul_nonneg he he,
    mul_nonneg hw (by linarith : (0 : ℤ) ≤ 30029 + e + (30029 + e - w) + 1)]

theorem numerics_cap_Z (F D X : ℤ) (hD : 720 ≤ D) (hX0 : 0 ≤ X) (hX : X ≤ D + 509)
    (hF : F * D ^ 2 = 43571520 * X * (X + 1)) : F ≤ 3 * 43571520 := by
  by_contra hcap
  have hcap := not_le.mp hcap
  obtain ⟨e, he, rfl⟩ : ∃ e : ℤ, 0 ≤ e ∧ D = 720 + e := ⟨D - 720, by omega, by ring⟩
  obtain ⟨w, hw, rfl⟩ : ∃ w : ℤ, 0 ≤ w ∧ X = 1229 + e - w := ⟨1229 + e - X, by omega, by ring⟩
  have h1 : (3 * 43571520 + 1) * (720 + e) ^ 2 ≤ F * (720 + e) ^ 2 :=
    mul_le_mul_of_nonneg_right (by omega) (sq_nonneg _)
  nlinarith [mul_nonneg he he,
    mul_nonneg hw (by linarith : (0 : ℤ) ≤ 1229 + e + (1229 + e - w) + 1)]

theorem numerics_crt (F : ℕ) (hmod : F % 518400 = 45523) (h7 : 7 ∣ F) (h41 : 41 ^ 2 ∣ F) :
    4651130323 ≤ F := by
  have h1 : F ≡ 4651130323 [MOD 518400] := by
    unfold Nat.ModEq
    rw [hmod]
  have h3 : 7 * 1681 ∣ F :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h7 (by simpa using h41)
  have h2 : F ≡ 4651130323 [MOD 7 * 1681] := by
    unfold Nat.ModEq
    rw [Nat.mod_eq_zero_of_dvd h3]
  have h4 := (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num)).1 ⟨h1, h2⟩
  unfold Nat.ModEq at h4
  have h5 := Nat.mod_le F (518400 * (7 * 1681))
  rw [h4] at h5
  exact h5

theorem numerics_F_eq (F x : ℕ) (a : ℤ) (hx : 1 ≤ x) (hax : |a| ≤ (x : ℤ)) (ha : |a| ≤ 509)
    (hF : (F : ℤ) * ((x : ℤ) - a) ^ 2 = 43571520 * (x : ℤ) * ((x : ℤ) + 1))
    (hcop : Nat.Coprime F 30) (hmod : F % 518400 = 45523) (h7 : 7 ∣ F) :
    F = 7 * 1039 * 5851 := by
  obtain ⟨ha1, ha2⟩ := abs_le.mp hax
  obtain ⟨hb1, hb2⟩ := abs_le.mp ha
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = (x : ℤ) - a := ⟨((x : ℤ) - a).toNat, by omega⟩
  rw [← hd] at hF
  have hFN : F * d ^ 2 = 43571520 * (x * (x + 1)) := by
    have : ((F * d ^ 2 : ℕ) : ℤ) = ((43571520 * (x * (x + 1)) : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso
      subst h0
      have : 0 < 43571520 * (x * (x + 1)) := by positivity
      simp at hFN
      omega
    · exact h0
  have d720 := numerics_dvd_720 F x d hFN hcop hd0
  have hXd : (x : ℤ) ≤ (d : ℤ) + 509 := by omega
  have hXd' : (d : ℤ) - 509 ≤ (x : ℤ) := by omega
  by_cases h41 : 41 ∣ d
  · have hd29520 : 29520 ≤ d := by omega
    have hlow := numerics_lower_bound_Z F d x (by exact_mod_cast hd29520) hXd' hF
    have hup := numerics_upper_bound_Z F d x (by exact_mod_cast hd29520) (by positivity) hXd hF
    have hlow' : 81 * 518400 < F := by exact_mod_cast hlow
    have hup' : F < 88 * 518400 := by exact_mod_cast hup
    omega
  · have h41F : 41 ^ 2 ∣ F := by
      have h : 41 ^ 2 ∣ F * d ^ 2 := by
        rw [hFN]
        exact Dvd.dvd.mul_right ⟨25920, by norm_num⟩ _
      have hcopd : Nat.Coprime (41 ^ 2) (d ^ 2) :=
        Nat.Coprime.pow 2 2 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h41)
      exact hcopd.dvd_of_dvd_mul_right h
    have hFge : 4651130323 ≤ F := numerics_crt F hmod h7 h41F
    have hd720 : 720 ≤ d := Nat.le_of_dvd hd0 d720
    have hcap := numerics_cap_Z F d x (by exact_mod_cast hd720) (by positivity) hXd hF
    have hcap' : F ≤ 3 * 43571520 := by exact_mod_cast hcap
    exact absurd (hFge.trans hcap') (by norm_num)

end CFSG.GH74.GLS.Stage4.Q9
