module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GorensteinWalter.TwoClassFusion

open DihedralGroup

variable {m : ℕ}

private theorem even_val_iff_castHom_eq_zero (hm : 1 ≤ m) (a : ZMod (2 ^ m)) :
    Even a.val ↔ ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) a = 0 := by
  have : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff_even]

theorem even_val_add_two_mul (hm : 1 ≤ m) (a k : ZMod (2 ^ m)) :
    Even (a + 2 * k).val ↔ Even a.val := by
  rw [even_val_iff_castHom_eq_zero hm, even_val_iff_castHom_eq_zero hm, map_add, map_mul,
    map_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]

theorem even_val_two_mul_sub (hm : 1 ≤ m) (a k : ZMod (2 ^ m)) :
    Even (2 * k - a).val ↔ Even a.val := by
  rw [even_val_iff_castHom_eq_zero hm, even_val_iff_castHom_eq_zero hm, map_sub, map_mul,
    map_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_sub, neg_eq_zero]

theorem even_val_add_half (hm : 2 ≤ m) (a : ZMod (2 ^ m)) :
    Even (a + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))).val ↔ Even a.val := by
  have hm1 : 1 ≤ m := by omega
  have hc : ((2 ^ (m - 1) : ℕ) : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  rw [even_val_iff_castHom_eq_zero hm1, even_val_iff_castHom_eq_zero hm1, map_add,
    map_natCast, hc, add_zero]

theorem even_val_zero : Even (0 : ZMod (2 ^ m)).val := by
  rw [ZMod.val_zero]
  exact ⟨0, rfl⟩

theorem not_even_val_one (hm : 1 ≤ m) : ¬ Even (1 : ZMod (2 ^ m)).val := by
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
  exact Nat.not_even_one

theorem orderOf_r_half (hm : 1 ≤ m) :
    orderOf (r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) = 2 := by
  have hpow : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    rw [← two_mul, ← pow_succ']
    congr 1
    omega
  apply orderOf_eq_prime
  · rw [pow_two, r_mul_r, ← Nat.cast_add, hpow, ZMod.natCast_self, r_zero]
  · intro h
    rw [← r_zero, r.injEq, ZMod.natCast_eq_zero_iff] at h
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h
    omega

theorem exists_conj_sr_eq (hm : 1 ≤ m) (d : DihedralGroup (2 ^ m)) (k : ZMod (2 ^ m)) :
    ∃ k' : ZMod (2 ^ m), d⁻¹ * sr k * d = sr k' ∧ (Even k'.val ↔ Even k.val) := by
  rcases dihedralGroup_cases d with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · refine ⟨k + 2 * a, ?_, even_val_add_two_mul hm k a⟩
    rw [inv_r, r_mul_sr, sr_mul_r]
    congr 1
    ring
  · refine ⟨2 * a - k, ?_, even_val_two_mul_sub hm k a⟩
    rw [inv_sr, sr_mul_sr, r_mul_sr]
    congr 1
    ring

theorem isConj_sr_zero_or_one (k : ZMod (2 ^ m)) :
    IsConj (sr k) (sr 0) ∨ IsConj (sr k) (sr 1) := by
  have : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
  obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' k.val
  · left
    refine isConj_iff.mpr ⟨r (q : ZMod (2 ^ m)), ?_⟩
    rw [r_mul_sr, inv_r, sr_mul_r, ← ZMod.natCast_zmod_val k, hq]
    congr 1
    push_cast
    ring
  · right
    refine isConj_iff.mpr ⟨r (q : ZMod (2 ^ m)), ?_⟩
    rw [r_mul_sr, inv_r, sr_mul_r, ← ZMod.natCast_zmod_val k, hq]
    congr 1
    push_cast
    ring

theorem eq_r_half_or_sr_of_orderOf_eq_two (hm : 2 ≤ m) {d : DihedralGroup (2 ^ m)}
    (hd : orderOf d = 2) :
    d = r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ∨ ∃ k : ZMod (2 ^ m), d = sr k := by
  rcases dihedralGroup_cases d with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · left
    have hsq := pow_orderOf_eq_one (r a)
    rw [hd] at hsq
    rw [pow_two, r_mul_r, ← r_zero, r.injEq, ← two_mul] at hsq
    rcases (zmod_two_mul_eq_zero_iff hm a).mp hsq with rfl | rfl
    · rw [r_zero, orderOf_one] at hd
      omega
    · push_cast
      rfl
  · exact Or.inr ⟨a, rfl⟩

theorem eq_of_commute_sr (hm : 2 ≤ m) {d : DihedralGroup (2 ^ m)} {k : ZMod (2 ^ m)}
    (h : Commute (sr k) d) :
    d = 1 ∨ d = r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ∨ d = sr k ∨
      d = sr (k + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) := by
  have hc : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = (2 ^ (m - 1) : ZMod (2 ^ m)) := by
    push_cast
    rfl
  replace h := h.eq
  rcases dihedralGroup_cases d with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [sr_mul_r, r_mul_sr, sr.injEq] at h
    have h2 : (2 : ZMod (2 ^ m)) * a = 0 := by linear_combination h
    rcases (zmod_two_mul_eq_zero_iff hm a).mp h2 with rfl | rfl
    · exact Or.inl r_zero
    · exact Or.inr (Or.inl (by rw [hc]))
  · rw [sr_mul_sr, sr_mul_sr, r.injEq] at h
    have h2 : (2 : ZMod (2 ^ m)) * (a - k) = 0 := by linear_combination h
    rcases (zmod_two_mul_eq_zero_iff hm (a - k)).mp h2 with h0 | h0
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [sr.injEq]
      linear_combination h0
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [sr.injEq, hc]
      linear_combination h0

end CFSG.GorensteinWalter.TwoClassFusion
