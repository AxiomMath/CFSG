module

public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

theorem padicValNat_add_two_le {r p f : ℕ} (hr : 2 ≤ r) (hp : Odd p) (hf : Even f)
    (h : p ^ f % 2 ^ (r + 1) = 2 ^ r + 1) : padicValNat 2 f + 2 ≤ r := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow_lt : 1 < 2 ^ (r + 1) := Nat.one_lt_pow (by omega) (by norm_num)
  have hp_ne_one : p ≠ 1 := by
    rintro rfl
    rw [one_pow, Nat.mod_eq_of_lt hpow_lt] at h
    have : 0 < 2 ^ r := pow_pos (by norm_num) r
    omega
  have hf_ne_zero : f ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.mod_eq_of_lt hpow_lt] at h
    have : 0 < 2 ^ r := pow_pos (by norm_num) r
    omega
  have hp_gt_one : 1 < p := by
    rcases hp with ⟨k, hk⟩
    omega
  have hx : ¬ 2 ∣ p := by
    rintro ⟨k, hk⟩
    rcases hp with ⟨j, hj⟩
    omega
  have hxy : 2 ∣ p - 1 := by
    rcases hp with ⟨j, hj⟩
    exact ⟨j, by omega⟩
  have hp1' : p - 1 ≠ 0 := by omega
  have hp2' : p + 1 ≠ 0 := by omega
  set q : ℕ := p ^ f / 2 ^ (r + 1) with hq
  have hdiv : 2 ^ (r + 1) * q + (2 ^ r + 1) = p ^ f := by
    have hd := Nat.div_add_mod (p ^ f) (2 ^ (r + 1))
    rw [h] at hd
    rw [hq]
    exact hd
  have hpf : p ^ f = 2 ^ r * (2 * q + 1) + 1 := by
    rw [← hdiv, pow_succ]
    ring
  have hsub : p ^ f - 1 = 2 ^ r * (2 * q + 1) := by
    rw [hpf, Nat.add_sub_cancel]
  have hval : padicValNat 2 (p ^ f - 1) = r := by
    have hodd : Odd (2 * q + 1) := ⟨q, by ring⟩
    have hndvd : ¬ 2 ∣ 2 * q + 1 := fun hd =>
      (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
    rw [hsub, padicValNat.mul (pow_ne_zero _ (by norm_num)) (by positivity),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hndvd]
    omega
  have hlte := padicValNat.pow_two_sub_pow (x := p) (y := 1) hp_gt_one hxy hx
    (n := f) hf_ne_zero hf
  rw [one_pow, hval] at hlte
  have hsum : 3 ≤ padicValNat 2 (p + 1) + padicValNat 2 (p - 1) := by
    have h4 : 4 ∣ p + 1 ∨ 4 ∣ p - 1 := by
      rcases hp with ⟨k, hk⟩
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · right; exact ⟨j, by omega⟩
      · left; exact ⟨j + 1, by omega⟩
    have e1 : 1 ≤ padicValNat 2 (p + 1) := by
      have : 2 ^ 1 ∣ p + 1 := by
        rcases hp with ⟨k, hk⟩
        exact ⟨k + 1, by omega⟩
      exact (padicValNat_dvd_iff_le (p := 2) (a := p + 1) (n := 1) hp2').mp this
    have e2 : 1 ≤ padicValNat 2 (p - 1) :=
      (padicValNat_dvd_iff_le (p := 2) (a := p - 1) (n := 1) hp1').mp (by simpa using hxy)
    rcases h4 with h4 | h4
    · have : 2 ≤ padicValNat 2 (p + 1) :=
        (padicValNat_dvd_iff_le (p := 2) (a := p + 1) (n := 2) hp2').mp (by
          have : (4 : ℕ) = 2 ^ 2 := by norm_num
          rw [← this]; exact h4)
      omega
    · have : 2 ≤ padicValNat 2 (p - 1) :=
        (padicValNat_dvd_iff_le (p := 2) (a := p - 1) (n := 2) hp1').mp (by
          have : (4 : ℕ) = 2 ^ 2 := by norm_num
          rw [← this]; exact h4)
      omega
  omega

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
