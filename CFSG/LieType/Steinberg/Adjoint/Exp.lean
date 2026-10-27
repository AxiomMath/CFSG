module

public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.Algebra.Algebra.Bilinear

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open IsNilpotent

variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem units_mul_exp_mul_inv (u : Aˣ) {a : A} (ha : IsNilpotent a) :
    (u : A) * exp a * ((u⁻¹ : Aˣ) : A) = exp ((u : A) * a * ((u⁻¹ : Aˣ) : A)) := by
  obtain ⟨n, hn⟩ := ha
  have hn' : ((u : A) * a * ((u⁻¹ : Aˣ) : A)) ^ n = 0 := by
    rw [Units.conj_pow, hn, mul_zero, zero_mul]
  rw [exp_eq_sum hn, exp_eq_sum hn', Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Units.conj_pow, mul_smul_comm, smul_mul_assoc]

theorem exp_mulLeft {b : A} (hb : IsNilpotent b) :
    exp (LinearMap.mulLeft ℚ b) = LinearMap.mulLeft ℚ (exp b) := by
  obtain ⟨n, hn⟩ := hb
  have hn' : LinearMap.mulLeft ℚ b ^ n = 0 := by
    rw [LinearMap.pow_mulLeft, hn, LinearMap.mulLeft_zero_eq_zero]
  refine LinearMap.ext fun x => ?_
  rw [exp_eq_sum hn', exp_eq_sum hn, LinearMap.sum_apply, LinearMap.mulLeft_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, LinearMap.pow_mulLeft, LinearMap.mulLeft_apply, smul_mul_assoc]

theorem exp_mulRight {b : A} (hb : IsNilpotent b) :
    exp (LinearMap.mulRight ℚ b) = LinearMap.mulRight ℚ (exp b) := by
  obtain ⟨n, hn⟩ := hb
  have hn' : LinearMap.mulRight ℚ b ^ n = 0 := by
    rw [LinearMap.pow_mulRight, hn, LinearMap.mulRight_zero_eq_zero]
  refine LinearMap.ext fun x => ?_
  rw [exp_eq_sum hn', exp_eq_sum hn, LinearMap.sum_apply, LinearMap.mulRight_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, LinearMap.pow_mulRight, LinearMap.mulRight_apply, mul_smul_comm]

theorem neg_mulRight (b : A) : -LinearMap.mulRight ℚ b = LinearMap.mulRight ℚ (-b) :=
  LinearMap.ext fun x => by simp

theorem exp_mul_mul_exp_neg {a b : A} (hb : IsNilpotent b)
    (h : b * (b * (b * a - a * b) - (b * a - a * b) * b) =
      (b * (b * a - a * b) - (b * a - a * b) * b) * b) :
    exp b * a * exp (-b) =
      a + (b * a - a * b) + (2 : ℚ)⁻¹ • (b * (b * a - a * b) - (b * a - a * b) * b) := by
  set L := LinearMap.mulLeft ℚ b
  set M := LinearMap.mulRight ℚ b
  have hc : Commute L M := LinearMap.commute_mulLeft_right b b
  obtain ⟨n, hn⟩ := hb
  have hL : IsNilpotent L := ⟨n, by rw [LinearMap.pow_mulLeft, hn, LinearMap.mulLeft_zero_eq_zero]⟩
  have hM : IsNilpotent M :=
    ⟨n, by rw [LinearMap.pow_mulRight, hn, LinearMap.mulRight_zero_eq_zero]⟩
  have hb : IsNilpotent b := ⟨n, hn⟩
  have key : exp b * a * exp (-b) = exp (L - M) a := by
    rw [sub_eq_add_neg, exp_add_of_commute hc.neg_right hL hM.neg, neg_mulRight,
      exp_mulLeft hb, exp_mulRight hb.neg, Module.End.mul_apply, LinearMap.mulRight_apply,
      LinearMap.mulLeft_apply, mul_assoc]
  have hLM : ∀ x, (L - M) x = b * x - x * b := fun x => rfl
  have h3 : (L - M) ^ 3 • a = 0 := by
    rw [Module.End.smul_def, _root_.pow_succ, _root_.pow_succ, pow_one, Module.End.mul_apply,
      Module.End.mul_apply, hLM, hLM, hLM, h, sub_self]
  rw [key, ← Module.End.smul_def, exp_smul_eq_sum h3 (hc.isNilpotent_sub hL hM)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one, inv_one,
    one_smul, pow_zero, pow_one, Module.End.smul_def, Module.End.one_apply, zero_add,
    Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMul, sq, Module.End.mul_apply, hLM]
  norm_num

theorem commutator_exp {a b z w : A} (ha : IsNilpotent a) (hb : IsNilpotent b)
    (hz : IsNilpotent z) (hw : IsNilpotent w) (hz' : a * b - b * a = z)
    (hw' : b * z - z * b = w) (haz : Commute a z) (haw : Commute a w) (hzw : Commute z w)
    (hbw : Commute b w) :
    exp a * exp b * exp (-a) * exp (-b) = exp z * exp ((2 : ℚ)⁻¹ • w) := by
  let u : Aˣ := ⟨exp b, exp (-b), exp_mul_exp_neg_self hb, exp_neg_mul_exp_self hb⟩
  have h1 : exp b * exp (-a) * exp (-b) = exp (exp b * (-a) * exp (-b)) :=
    units_mul_exp_mul_inv u ha.neg
  have hba : b * -a - -a * b = z := by
    rw [← hz', mul_neg, neg_mul, sub_neg_eq_add]
    abel
  have h2 : exp b * (-a) * exp (-b) = -a + z + (2 : ℚ)⁻¹ • w := by
    rw [exp_mul_mul_exp_neg hb (by rw [hba, hw']; exact hbw.eq), hba, hw']
  have hw2 : IsNilpotent ((2 : ℚ)⁻¹ • w) := hw.smul _
  have hc1 : Commute (-a) z := haz.neg_left
  have hc2 : Commute (-a + z) ((2 : ℚ)⁻¹ • w) :=
    ((haw.neg_left).add_left hzw).smul_right _
  calc exp a * exp b * exp (-a) * exp (-b) = exp a * (exp b * exp (-a) * exp (-b)) := by
        simp only [mul_assoc]
    _ = exp a * (exp (-a) * exp z * exp ((2 : ℚ)⁻¹ • w)) := by
        rw [h1, h2, exp_add_of_commute hc2 (hc1.isNilpotent_add ha.neg hz) hw2,
          exp_add_of_commute hc1 ha.neg hz]
    _ = exp z * exp ((2 : ℚ)⁻¹ • w) := by
        rw [← mul_assoc, ← mul_assoc, exp_mul_exp_neg_self ha, one_mul]

theorem commute_exp {a b : A} (h : Commute a b) (ha : IsNilpotent a) (hb : IsNilpotent b) :
    Commute (exp a) (exp b) := by
  rw [Commute, SemiconjBy, ← exp_add_of_commute h ha hb, ← exp_add_of_commute h.symm hb ha,
    add_comm]

theorem commutator_exp' {a b z u : A} (ha : IsNilpotent a) (hb : IsNilpotent b)
    (hz : IsNilpotent z) (hu : IsNilpotent u) (hz' : a * b - b * a = z)
    (hu' : a * z - z * a = u) (hbz : Commute b z) (hbu : Commute b u) (hzu : Commute z u)
    (hau : Commute a u) :
    exp a * exp b * exp (-a) * exp (-b) = exp z * exp ((2 : ℚ)⁻¹ • u) := by
  let v : Aˣ := ⟨exp a, exp (-a), exp_mul_exp_neg_self ha, exp_neg_mul_exp_self ha⟩
  have h1 : exp a * exp b * exp (-a) = exp (exp a * b * exp (-a)) :=
    units_mul_exp_mul_inv v hb
  have h2 : exp a * b * exp (-a) = b + z + (2 : ℚ)⁻¹ • u := by
    rw [exp_mul_mul_exp_neg ha (by rw [hz', hu']; exact hau.eq), hz', hu']
  have hu2 : IsNilpotent ((2 : ℚ)⁻¹ • u) := hu.smul _
  have hc2 : Commute (b + z) ((2 : ℚ)⁻¹ • u) := (hbu.add_left hzu).smul_right _
  calc exp a * exp b * exp (-a) * exp (-b) = exp (b + z + (2 : ℚ)⁻¹ • u) * exp (-b) := by
        rw [h1, h2]
    _ = exp b * (exp z * exp ((2 : ℚ)⁻¹ • u)) * exp (-b) := by
        rw [exp_add_of_commute hc2 (hbz.isNilpotent_add hb hz) hu2, exp_add_of_commute hbz hb hz,
          mul_assoc (exp b)]
    _ = exp z * exp ((2 : ℚ)⁻¹ • u) := by
        rw [((commute_exp hbz hb hz).mul_right (commute_exp (hbu.smul_right _) hb hu2)).eq,
          mul_assoc, exp_mul_exp_neg_self hb, mul_one]

end CFSG.LieType.Steinberg.Adjoint
