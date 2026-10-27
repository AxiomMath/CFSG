module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Abel

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

structure QuatRel {R : Type*} [Ring R] (s t : R) : Prop where
  ss : s * s = -1
  tt : t * t = -1
  ts : t * s = -(s * t)

variable {K R : Type*} [Field K] [Ring R] [Algebra K R] {s t : R}

theorem QuatRel.sts (h : QuatRel s t) : s * t * s = t := by
  rw [mul_assoc, h.ts, mul_neg, ← mul_assoc, h.ss, neg_mul, one_mul, neg_neg]

theorem QuatRel.stst (h : QuatRel s t) : s * t * (s * t) = -1 := by
  rw [← mul_assoc, h.sts, h.tt]

theorem QuatRel.stt (h : QuatRel s t) : s * t * t = -s := by
  rw [mul_assoc, h.tt, mul_neg, mul_one]

theorem QuatRel.h_s (h : QuatRel s t) :
    (-1 + s + t + s * t) * s = (s * t) * (-1 + s + t + s * t) := by
  simp only [add_mul, mul_add, neg_mul, one_mul, mul_neg, mul_one, h.ss, h.ts, h.sts, h.stst,
    h.stt]
  abel

theorem QuatRel.h_t (h : QuatRel s t) :
    (-1 + s + t + s * t) * t = s * (-1 + s + t + s * t) := by
  have h1 : s * (s * t) = -t := by rw [← mul_assoc, h.ss, neg_mul, one_mul]
  simp only [add_mul, mul_add, neg_mul, one_mul, mul_neg, mul_one, h.tt, h.stt, h.ss, h1]
  abel

theorem QuatRel.h_sq (h : QuatRel s t) :
    (-1 + s + t + s * t) * (-1 + s + t + s * t) + 2 • (-1 + s + t + s * t) + 4 • (1 : R) = 0 := by
  have h1 : s * (s * t) = -t := by rw [← mul_assoc, h.ss, neg_mul, one_mul]
  have h2 : t * (s * t) = s := by rw [← mul_assoc, h.ts, neg_mul, h.stt, neg_neg]
  simp only [add_mul, mul_add, neg_mul, one_mul, mul_neg, mul_one, h.ss, h.tt, h1, h2, h.sts,
    h.ts, h.stt, h.stst]
  abel

@[expose] def quatC (half : K) (s t : R) : R := half • (-1 + s + t + s * t)

theorem QuatRel.c_sq (h : QuatRel s t) {half : K} (hh : (2 : K) * half = 1) :
    quatC half s t * quatC half s t + quatC half s t + 1 = 0 := by
  have h1 := h.h_sq
  unfold quatC
  rw [smul_mul_smul_comm]
  have h2 : (-1 + s + t + s * t) * (-1 + s + t + s * t) =
      -((2 : K) • (-1 + s + t + s * t)) - (4 : K) • (1 : R) := by
    have : (2 : ℕ) • (-1 + s + t + s * t) = (2 : K) • (-1 + s + t + s * t) := by
      rw [← Nat.cast_smul_eq_nsmul K]; norm_num
    have h4 : (4 : ℕ) • (1 : R) = (4 : K) • (1 : R) := by
      rw [← Nat.cast_smul_eq_nsmul K]; norm_num
    rw [← this, ← h4]
    calc (-1 + s + t + s * t) * (-1 + s + t + s * t)
        = ((-1 + s + t + s * t) * (-1 + s + t + s * t) + 2 • (-1 + s + t + s * t) + 4 • (1 : R))
          - 2 • (-1 + s + t + s * t) - 4 • (1 : R) := by abel
      _ = -(2 • (-1 + s + t + s * t)) - 4 • (1 : R) := by rw [h1]; abel
  rw [h2]
  have e1 : half * half * 2 = half := by linear_combination half * hh
  have e2 : half * half * 4 = 1 := by linear_combination (1 + 2 * half) * hh
  rw [smul_sub, smul_neg, smul_smul, smul_smul, e1, e2, one_smul]
  abel

theorem QuatRel.c_cubed (h : QuatRel s t) {half : K} (hh : (2 : K) * half = 1) :
    quatC half s t * quatC half s t * quatC half s t = 1 := by
  have h1 := h.c_sq hh
  have h2 : quatC half s t * quatC half s t = -quatC half s t - 1 := by
    rw [eq_sub_iff_add_eq, ← sub_eq_zero]
    rw [← h1]
    abel
  rw [mul_assoc, h2, mul_sub, mul_neg, mul_one, h2]
  abel

theorem QuatRel.c_s (h : QuatRel s t) (half : K) :
    quatC half s t * s = (s * t) * quatC half s t := by
  unfold quatC
  rw [smul_mul_assoc, mul_smul_comm, h.h_s]

theorem QuatRel.c_t (h : QuatRel s t) (half : K) :
    quatC half s t * t = s * quatC half s t := by
  unfold quatC
  rw [smul_mul_assoc, mul_smul_comm, h.h_t]

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
