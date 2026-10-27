module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Base
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.TotallySplit

public section

open scoped MatrixGroups

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Quasithin.H11

variable {F : Type} [Field F]

theorem l2op_mul_self (M : Matrix (Fin 2) (Fin 2) F) (hdet : M.det = 1) :
    M * M = M.trace • M - 1 := by
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first | ring1 | linear_combination (-1 : F) * hdet

theorem l2op_trace_mul_inv (x y : SL(2, F)) :
    ((x * y⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace =
      (x : Matrix (Fin 2) (Fin 2) F).trace * (y : Matrix (Fin 2) (Fin 2) F).trace -
        ((x * y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp
  ring

variable [CharP F 2]

theorem l2op_trace_eq_one {x : SL(2, F)} (h3 : x ^ 3 = 1) (hx : x ≠ 1) :
    (x : Matrix (Fin 2) (Fin 2) F).trace = 1 := by
  set M : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F) with hM
  set t := M.trace with ht
  have hsq : M * M = t • M - 1 := l2op_mul_self M x.2
  have h3' : M * M * M = 1 := by
    have := congrArg (fun y : SL(2, F) => (y : Matrix (Fin 2) (Fin 2) F)) h3
    simpa [pow_succ, Matrix.SpecialLinearGroup.coe_mul] using this
  have hcube : M * M * M = (t ^ 2 - 1) • M - t • (1 : Matrix (Fin 2) (Fin 2) F) := by
    calc M * M * M = M * (M * M) := Matrix.mul_assoc _ _ _
      _ = M * (t • M - 1) := by rw [hsq]
      _ = t • (M * M) - M := by rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
      _ = t • (t • M - 1) - M := by rw [hsq]
      _ = (t ^ 2 - 1) • M - t • (1 : Matrix (Fin 2) (Fin 2) F) := by module
  by_contra hne
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h1 : t + 1 ≠ 0 := fun h => hne (by linear_combination h - h2)
  have h4 : (t + 1) • ((t - 1) • M) = (t + 1) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have : (t ^ 2 - 1) • M = (1 : Matrix (Fin 2) (Fin 2) F) + t • (1 : Matrix (Fin 2) (Fin 2) F) :=
      sub_eq_iff_eq_add.1 (hcube.symm.trans h3')
    calc (t + 1) • ((t - 1) • M) = (t ^ 2 - 1) • M := by module
      _ = _ := by rw [this]; module
  have h5 : (t - 1) • M = 1 := smul_right_injective _ h1 h4
  have hc : (t - 1) ^ 2 = 1 ^ 2 := by
    have := congrArg Matrix.det h5
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at this
    have hdM : M.det = 1 := x.2
    rw [hdM, mul_one] at this
    rw [this, one_pow]
  have hc1 : t - 1 = 1 := CharTwo.sq_injective hc
  rw [hc1, one_smul] at h5
  exact hx (Subtype.ext h5)

theorem l2op_pow_three_of_trace {y : SL(2, F)}
    (ht : (y : Matrix (Fin 2) (Fin 2) F).trace = 1) : y ^ 3 = 1 := by
  have hsq := l2op_mul_self (y : Matrix (Fin 2) (Fin 2) F) y.2
  rw [ht, one_smul] at hsq
  apply Subtype.ext
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hcube : (y : Matrix (Fin 2) (Fin 2) F) * y * y = 1 := by
    rw [hsq, Matrix.sub_mul, hsq, Matrix.one_mul, sub_sub_cancel_left]
    have h1 : (-1 : F) = 1 := CharTwo.neg_eq 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1]
  simpa [pow_succ, Matrix.SpecialLinearGroup.coe_mul] using hcube

theorem l2op_ne_one_of_trace {y : SL(2, F)}
    (ht : (y : Matrix (Fin 2) (Fin 2) F).trace = 1) : y ≠ 1 := by
  rintro rfl
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.trace_one, Fintype.card_fin] at ht
  have h3 : (2 : F) = 1 := by exact_mod_cast ht
  exact one_ne_zero (h3.symm.trans h2)

theorem l2op_orderOf_eq_three {y : SL(2, F)}
    (ht : (y : Matrix (Fin 2) (Fin 2) F).trace = 1) : orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (l2op_pow_three_of_trace ht) (l2op_ne_one_of_trace ht)

theorem l2op_card_le_three (E : Subgroup SL(2, F)) (hE : ∀ x ∈ E, x ^ 3 = 1) :
    Nat.card E ≤ 3 := by
  rcases Subgroup.bot_or_exists_ne_one E with hE1 | ⟨x, hxE, hx1⟩
  · rw [hE1, Subgroup.card_bot]
    norm_num
  have htr : ∀ z ∈ E, z ≠ 1 → (z : Matrix (Fin 2) (Fin 2) F).trace = 1 :=
    fun z hz hz1 => l2op_trace_eq_one (hE z hz) hz1
  have hle : E ≤ Subgroup.zpowers x := by
    intro y hy
    by_contra hyx
    have hy1 : y ≠ 1 := fun h => hyx (h ▸ one_mem _)
    have hxy : x * y ≠ 1 := fun h => hyx (by
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_mem (Subgroup.mem_zpowers x))
    have hxy' : x * y⁻¹ ≠ 1 := fun h => hyx (by
      rw [← mul_inv_eq_one.1 h]
      exact Subgroup.mem_zpowers x)
    have key := l2op_trace_mul_inv x y
    rw [htr _ (E.mul_mem hxE (E.inv_mem hy)) hxy', htr x hxE hx1, htr y hy hy1,
      htr _ (E.mul_mem hxE hy) hxy] at key
    exact one_ne_zero (by linear_combination key : (1 : F) = 0)
  have hord : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hE x hxE)
  have hfin : Finite (Subgroup.zpowers x) :=
    Nat.finite_of_card_ne_zero (by
      rw [Nat.card_zpowers]
      exact (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hE x hxE⟩)).ne')
  calc Nat.card E ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
    _ = orderOf x := Nat.card_zpowers x
    _ ≤ 3 := Nat.le_of_dvd (by norm_num) hord

theorem l2op_trace_comm_uSL (x : SL(2, F)) (c : F) :
    ((x * uSL c * x⁻¹ * (uSL c)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace =
      (x 1 0 * c) ^ 2 := by
  have hdet := x.2
  rw [Matrix.det_fin_two] at hdet
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, coe_uSL, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp
  linear_combination (2 : F) * hdet + h2

theorem l2op_trace_comm_lSL (x : SL(2, F)) (c : F) :
    ((x * lSL c * x⁻¹ * (lSL c)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace =
      (x 0 1 * c) ^ 2 := by
  have hdet := x.2
  rw [Matrix.det_fin_two] at hdet
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, coe_lSL, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp
  linear_combination (2 : F) * hdet + h2

end CFSG.HardMathSupport.Solomon.Coordinator
