module

public import Mathlib.NumberTheory.Multiplicity

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Proving

private lemma padicValNat_three_eq_one {m : ℕ} (hm : m ≠ 0) (h3 : 3 ∣ m) (h9 : ¬ 9 ∣ m) :
    padicValNat 3 m = 1 := by
  have hle : 1 ≤ padicValNat 3 m := (padicValNat_dvd_iff_le hm).mp (by simpa using h3)
  have hlt : padicValNat 3 m < 2 := by
    by_contra h
    have h2 : 3 ^ 2 ∣ m := (padicValNat_dvd_iff_le hm).mpr (by omega)
    exact h9 (by simpa using h2)
  omega

public theorem three_part_SL3_of_three_cover (q : ℕ) (hq : 1 < q) (h3 : 3 ∣ q - 1)
    (h9 : ¬ 9 ∣ q - 1) :
    padicValNat 3 (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)) = 3 := by
  have hv1 : padicValNat 3 (q - 1) = 1 := padicValNat_three_eq_one (by omega) h3 h9
  have hnd : ¬ 3 ∣ q := by omega
  have hq3 : q ^ 3 ≠ 0 := pow_ne_zero 3 (by omega)
  have hq2 : q ^ 2 - 1 ≠ 0 := by
    have : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    omega
  have hq3' : q ^ 3 - 1 ≠ 0 := by
    have : q ≤ q ^ 3 := Nat.le_self_pow (by norm_num) q
    omega
  have hsq : padicValNat 3 (q ^ 2 - 1) = 1 := by
    have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
      have e : (m + 1) ^ 2 = m * (m + 1 + 1) + 1 := by ring
      rw [e, Nat.add_sub_cancel, Nat.add_sub_cancel]
    have hnq1 : ¬ 3 ∣ q + 1 := by omega
    rw [hfac, padicValNat.mul (by omega) (by omega), hv1,
      padicValNat.eq_zero_of_not_dvd hnq1]
  have hcube : padicValNat 3 (q ^ 3 - 1) = 2 := by
    have h := padicValNat.pow_sub_pow (p := 3) (x := q) (y := 1) ⟨1, by norm_num⟩
      (by omega) (by simpa using h3) hnd (by norm_num : (3 : ℕ) ≠ 0)
    rw [one_pow] at h
    rw [h, hv1, padicValNat_self]
  have hq3val : padicValNat 3 (q ^ 3) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => hnd (Nat.prime_three.dvd_of_dvd_pow h))
  rw [padicValNat.mul (mul_ne_zero hq3 hq2) hq3', padicValNat.mul hq3 hq2, hq3val, hsq, hcube]

public theorem three_part_SU3_of_three_cover (q : ℕ) (hq : 1 < q) (h3 : 3 ∣ q + 1)
    (h9 : ¬ 9 ∣ q + 1) :
    padicValNat 3 (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) = 3 := by
  have hv1 : padicValNat 3 (q + 1) = 1 := padicValNat_three_eq_one (by omega) h3 h9
  have hnd : ¬ 3 ∣ q := by omega
  have hq3 : q ^ 3 ≠ 0 := pow_ne_zero 3 (by omega)
  have hq2 : q ^ 2 - 1 ≠ 0 := by
    have : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    omega
  have hq3' : q ^ 3 + 1 ≠ 0 := by omega
  have hsq : padicValNat 3 (q ^ 2 - 1) = 1 := by
    have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
      have e : (m + 1) ^ 2 = m * (m + 1 + 1) + 1 := by ring
      rw [e, Nat.add_sub_cancel, Nat.add_sub_cancel]
    have hnq1 : ¬ 3 ∣ q - 1 := by omega
    rw [hfac, padicValNat.mul (by omega) (by omega), hv1,
      padicValNat.eq_zero_of_not_dvd hnq1]
  have hcube : padicValNat 3 (q ^ 3 + 1) = 2 := by
    have h := padicValNat.pow_add_pow (p := 3) (x := q) (y := 1) (n := 3) ⟨1, by norm_num⟩
      (by simpa using h3) hnd ⟨1, by norm_num⟩
    rw [one_pow] at h
    rw [h, hv1, padicValNat_self]
  have hq3val : padicValNat 3 (q ^ 3) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => hnd (Nat.prime_three.dvd_of_dvd_pow h))
  rw [padicValNat.mul (mul_ne_zero hq3 hq2) hq3', padicValNat.mul hq3 hq2, hq3val, hsq, hcube]

end CFSG.HardMathSupport.Foote.Proving
