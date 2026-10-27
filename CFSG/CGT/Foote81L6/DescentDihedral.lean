module

public import CFSG.Assembly.Defs
public import CFSG.CGT.Foote81L6.Dihedral

public section

namespace CFSG.CGT.Foote81L6

open Subgroup DihedralGroup

variable {k : ℕ}

theorem zc_eq_r (k : ℕ) : zc (k + 2) = r ((2 ^ (k + 1) : ℕ) : ZMod (2 ^ (k + 2))) := by
  rw [← rho_pow (by omega : 1 ≤ k + 2), r_pow, one_mul]
  rfl

theorem half_add_half (k : ℕ) :
    ((2 ^ (k + 1) : ℕ) : ZMod (2 ^ (k + 2))) + ((2 ^ (k + 1) : ℕ) : ZMod (2 ^ (k + 2))) = 0 :=
  two_pow_add_self (k + 1)

theorem quarter_add_quarter (k : ℕ) :
    ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) + ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) =
      ((2 ^ (k + 1) : ℕ) : ZMod (2 ^ (k + 2))) := by
  rw [← Nat.cast_add, show 2 ^ k + 2 ^ k = 2 ^ (k + 1) by ring]

theorem r_mul_self_eq_zc_iff {i : ZMod (2 ^ (k + 2))} :
    (r i : DihedralGroup (2 ^ (k + 2))) * r i = zc (k + 2) ↔
      i = ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) ∨
        i = ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) + ((2 ^ (k + 1) : ℕ) : ZMod (2 ^ (k + 2))) := by
  rw [r_mul_r, zc_eq_r, r.injEq]
  set q : ZMod (2 ^ (k + 2)) := ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2)))
  set h : ZMod (2 ^ (k + 2)) := ((2 ^ (k + 1) : ℕ) : ZMod (2 ^ (k + 2)))
  have hqq : q + q = h := quarter_add_quarter k
  have hhh : h + h = 0 := half_add_half k
  constructor
  · intro hi
    have h0 : (i - q) + (i - q) = 0 := by
      calc (i - q) + (i - q) = (i + i) - (q + q) := by ring
        _ = 0 := by rw [hi, hqq, sub_self]
    rcases eq_zero_or_half (b := k + 1) h0 with h1 | h1
    · left
      exact sub_eq_zero.1 h1
    · right
      calc i = (i - q) + q := by ring
        _ = q + h := by rw [h1]; ring
  · rintro (rfl | rfl)
    · exact hqq
    · calc q + h + (q + h) = (q + q) + (h + h) := by ring
        _ = h := by rw [hqq, hhh, add_zero]

theorem r_mul_self_eq_one_iff {i : ZMod (2 ^ (k + 2))} :
    (r i : DihedralGroup (2 ^ (k + 2))) * r i = 1 ↔
      (r i : DihedralGroup (2 ^ (k + 2))) = 1 ∨ (r i : DihedralGroup (2 ^ (k + 2))) = zc (k + 2) := by
  rw [r_mul_r, one_def, r.injEq, zc_eq_r, r.injEq, r.injEq]
  constructor
  · intro hi
    exact eq_zero_or_half (b := k + 1) hi
  · rintro (rfl | rfl)
    · exact add_zero 0
    · exact half_add_half k

theorem isConj_sr_mul_zc (i : ZMod (2 ^ (k + 2))) :
    IsConj (sr i : DihedralGroup (2 ^ (k + 2))) (sr i * zc (k + 2)) := by
  rw [isConj_iff]
  refine ⟨r (-((2 ^ k : ℕ) : ZMod (2 ^ (k + 2)))), ?_⟩
  rw [zc_eq_r, inv_r, r_mul_sr, sr_mul_r, sr_mul_r]
  congr 1
  have hqq := quarter_add_quarter k
  calc i - -((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) + -(-((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))))
      = i + (((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) + ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2)))) := by ring
    _ = i + ((2 ^ (k + 1) : ℕ) : ZMod (2 ^ (k + 2))) := by rw [hqq]

theorem r_quarter_mul_self : (r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) :
    DihedralGroup (2 ^ (k + 2))) * r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) = zc (k + 2) :=
  r_mul_self_eq_zc_iff.2 (Or.inl rfl)

theorem orderOf_r_quarter :
    orderOf (r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) : DihedralGroup (2 ^ (k + 2))) = 4 := by
  have h2 : (r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) : DihedralGroup (2 ^ (k + 2))) ^ 2 =
      zc (k + 2) := by rw [sq]; exact r_quarter_mul_self
  have h4 : (r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) : DihedralGroup (2 ^ (k + 2))) ^ (2 ^ 2) = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, h2, sq, zc_mul_self (by omega)]
  have hne : (r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) : DihedralGroup (2 ^ (k + 2))) ^ (2 ^ 1) ≠ 1 := by
    rw [pow_one, h2]
    exact zc_ne_one (by omega)
  have := orderOf_eq_prime_pow (p := 2) (n := 1) hne h4
  simpa using this

theorem eq_quarter_of_orderOf_eq_four {g : DihedralGroup (2 ^ (k + 2))} (hg : orderOf g = 4) :
    g = r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) ∨ g = (r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))))⁻¹ := by
  rcases g with i | i
  · have h4 : (r i : DihedralGroup (2 ^ (k + 2))) ^ 4 = 1 := by rw [← hg]; exact pow_orderOf_eq_one _
    have hsq : (r i * r i) * (r i * r i) = (1 : DihedralGroup (2 ^ (k + 2))) := by
      rw [← h4]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rcases r_mul_self_eq_one_iff.1 (show r (i + i) * r (i + i) = (1 : DihedralGroup (2 ^ (k + 2))) by
      rw [← r_mul_r]; exact hsq) with h1 | h1
    · exfalso
      have : (r i : DihedralGroup (2 ^ (k + 2))) ^ 2 = 1 := by rw [sq, r_mul_r]; exact h1
      have := orderOf_dvd_of_pow_eq_one this
      rw [hg] at this
      norm_num at this
    · rw [← r_mul_r] at h1
      rcases r_mul_self_eq_zc_iff.1 h1 with h | h
      · left; rw [h]
      · right
        rw [h, inv_r]
        congr 1
        have hqq := quarter_add_quarter k
        have hhh := half_add_half k
        calc ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) + ((2 ^ (k + 1) : ℕ) : ZMod (2 ^ (k + 2)))
            = ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) + ((2 ^ (k + 1) : ℕ) : ZMod (2 ^ (k + 2))) -
              (((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) + ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) -
                ((2 ^ (k + 1) : ℕ) : ZMod (2 ^ (k + 2)))) := by rw [hqq, sub_self, sub_zero]
          _ = -((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) + (((2 ^ (k + 1) : ℕ) : ZMod (2 ^ (k + 2))) +
              ((2 ^ (k + 1) : ℕ) : ZMod (2 ^ (k + 2)))) := by ring
          _ = -((2 ^ k : ℕ) : ZMod (2 ^ (k + 2))) := by rw [hhh, add_zero]
  · exfalso
    rw [orderOf_sr] at hg
    omega

end CFSG.CGT.Foote81L6
