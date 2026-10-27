module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.ComponentClassification.HarrisLit

namespace L415

open DihedralGroup

theorem eq_of_add_self_eq_zero {m : ℕ} (hm : 1 ≤ m) {i : ZMod (2 ^ m)} (h : i + i = 0) :
    i = 0 ∨ i = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  have : NeZero (2 ^ m) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hN : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hv := ZMod.val_lt i
  have h1 : (i + i).val = 0 := by rw [h, ZMod.val_zero]
  rw [ZMod.val_add] at h1
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h1
  rw [← ZMod.natCast_zmod_val i]
  generalize i.val = v at hq hv
  generalize 2 ^ (m - 1) = N at hN ⊢
  rw [hN] at hq hv
  rcases q with _ | _ | q
  · left
    have h2 : v = 0 := by simp at hq; omega
    rw [h2, Nat.cast_zero]
  · right
    have h2 : v = N := by simp at hq; omega
    rw [h2]
  · exfalso
    have h2 : 2 * N * 2 ≤ 2 * N * (q + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
    omega

theorem eq_of_add_self_eq_half {m : ℕ} (hm : 2 ≤ m) {i : ZMod (2 ^ m)}
    (h : i + i = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) :
    i = ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) ∨
      i = ((2 ^ (m - 2) + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  have : NeZero (2 ^ m) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hN1 : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  have hN : 2 ^ m = 4 * 2 ^ (m - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have hv := ZMod.val_lt i
  have h1 := congrArg ZMod.val h
  have hlt : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at h1
  have h2 := Nat.div_add_mod (i.val + i.val) (2 ^ m)
  rw [h1] at h2
  rw [← ZMod.natCast_zmod_val i]
  generalize i.val = v at h2 hv
  generalize (v + v) / 2 ^ m = q at h2
  rw [hN1]
  generalize 2 ^ (m - 2) = N at hN1 hN ⊢
  rw [hN] at h2 hv
  rw [hN1] at h2
  rcases q with _ | _ | q
  · left
    have h3 : v = N := by simp at h2; omega
    rw [h3]
  · right
    have h3 : v = N + 2 * N := by simp at h2; omega
    rw [h3]
  · exfalso
    have h3 : 4 * N * 2 ≤ 4 * N * (q + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
    omega

theorem dih_central {m : ℕ} (hm : 2 ≤ m) {c : DihedralGroup (2 ^ m)}
    (hc : ∀ d : DihedralGroup (2 ^ m), c * d = d * c) :
    c = 1 ∨ c = r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  have : NeZero (2 ^ m) := ⟨pow_ne_zero _ two_ne_zero⟩
  rcases c with i | i
  · have h1 := hc (sr 0)
    rw [r_mul_sr, sr_mul_r, sr.injEq] at h1
    have h2 : i + i = 0 := by linear_combination -h1
    rcases eq_of_add_self_eq_zero (by omega) h2 with h | h
    · left
      rw [h, r_zero]
    · right
      rw [h]
  · exfalso
    have h1 := hc (r 1)
    rw [sr_mul_r, r_mul_sr, sr.injEq] at h1
    have h2 : ((2 : ℕ) : ZMod (2 ^ m)) = 0 := by
      push_cast
      linear_combination h1
    rw [ZMod.natCast_eq_zero_iff] at h2
    have h3 := Nat.le_of_dvd (by norm_num) h2
    have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega

theorem dih_sq_eq {m : ℕ} (hm : 2 ≤ m) {y : DihedralGroup (2 ^ m)}
    (hy : y * y = r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) :
    y = r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) ∨
      y = r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) * r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  have : NeZero (2 ^ m) := ⟨pow_ne_zero _ two_ne_zero⟩
  rcases y with i | i
  · rw [r_mul_r, r.injEq] at hy
    rcases eq_of_add_self_eq_half hm hy with h | h
    · left
      rw [h]
    · right
      rw [r_mul_r, h, Nat.cast_add]
  · exfalso
    rw [sr_mul_self, one_def, r.injEq] at hy
    have h1 := (ZMod.natCast_eq_zero_iff _ _).mp hy.symm
    have h2 := Nat.le_of_dvd (pow_pos two_pos _) h1
    have h3 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

theorem dih_sq_quarter {m : ℕ} (hm : 2 ≤ m) :
    r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) * r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) =
      r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  rw [r_mul_r, ← Nat.cast_add]
  congr 2
  rw [← two_mul, ← pow_succ']
  congr 1
  omega

end L415

end CFSG.ComponentClassification.HarrisLit
