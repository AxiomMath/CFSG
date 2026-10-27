module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

public noncomputable section

namespace CFSG.Alternating.Multipliers.Spin

open Equiv Equiv.Perm Subgroup

variable (n : ℕ)

abbrev sumSq : QuadraticForm ℚ (Fin n → ℚ) :=
  QuadraticMap.weightedSumSquares ℚ fun _ : Fin n => (1 : ℚ)

abbrev Cl : Type := CliffordAlgebra (sumSq n)

@[expose] def v (i : Fin n) : Cl n := CliffordAlgebra.ι (sumSq n) (Pi.single i 1)

variable {n}

theorem v_mul_self (i : Fin n) : v n i * v n i = 1 := by
  rw [v, CliffordAlgebra.ι_sq_scalar]
  simp [QuadraticMap.weightedSumSquares_apply, Pi.single_apply]

theorem v_mul_v {i j : Fin n} (h : i ≠ j) : v n i * v n j = -(v n j * v n i) := by
  have e := CliffordAlgebra.ι_mul_ι_add_swap (Q := sumSq n) (Pi.single i 1) (Pi.single j 1)
  have hp : QuadraticMap.polar (sumSq n) (Pi.single i 1) (Pi.single j 1) = 0 := by
    simp only [QuadraticMap.polar, QuadraticMap.weightedSumSquares_apply, Pi.add_apply,
      one_smul]
    simp [Pi.single_apply, Finset.sum_add_distrib, mul_add, Finset.sum_ite_eq', h, h.symm]
  rw [hp, map_zero] at e
  exact eq_neg_of_add_eq_zero_left e

theorem one_ne_neg_one : (1 : Cl n) ≠ -1 := by
  let _ : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  intro h
  have h2 : (2 : Cl n) = 0 := by
    rw [← one_add_one_eq_two]
    nth_rw 2 [h]
    exact add_neg_cancel 1
  have h1 : (1 : Cl n) = 0 := by
    rw [← map_one (algebraMap ℚ (Cl n)), show (1 : ℚ) = 2⁻¹ * 2 by norm_num, map_mul,
      map_ofNat, h2, mul_zero]
  exact one_ne_zero h1

theorem v_injective : Function.Injective (v n) := by
  intro i j h
  by_contra hij
  have e := v_mul_v hij
  rw [h, v_mul_self] at e
  exact one_ne_neg_one e

@[expose] def r (a b : Fin n) : Cl n := v n a - v n b

theorem r_mul_self {a b : Fin n} (h : a ≠ b) : r a b * r a b = 2 := by
  rw [r, sub_mul, mul_sub, mul_sub, v_mul_self, v_mul_self, v_mul_v h, ← one_add_one_eq_two]
  abel

theorem r_mul_v {a b : Fin n} (h : a ≠ b) (j : Fin n) :
    r a b * v n j = -(v n (swap a b j) * r a b) := by
  rcases eq_or_ne j a with rfl | hja
  · rw [swap_apply_left, r, sub_mul, mul_sub, v_mul_self, v_mul_self]
    abel
  rcases eq_or_ne j b with rfl | hjb
  · rw [swap_apply_right, r, sub_mul, mul_sub, v_mul_self, v_mul_self]
    abel
  rw [swap_apply_of_ne_of_ne hja hjb, r, sub_mul, mul_sub, v_mul_v (Ne.symm hja),
    v_mul_v (Ne.symm hjb)]
  abel

theorem r_mul_r {a b c d : Fin n} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    r a b * r c d = -(r c d * r a b) := by
  simp only [r, sub_mul, mul_sub, v_mul_v hac, v_mul_v had, v_mul_v hbc, v_mul_v hbd]
  abel

abbrev half : Cl n := algebraMap ℚ (Cl n) (1 / 2)

theorem half_mul_two : (half : Cl n) * 2 = 1 := by
  rw [← map_ofNat (algebraMap ℚ (Cl n)) 2, ← map_mul]
  norm_num

theorem two_mul_half : 2 * (half : Cl n) = 1 := by
  rw [← map_ofNat (algebraMap ℚ (Cl n)) 2, ← map_mul]
  norm_num

theorem half_comm (x : Cl n) : half * x = x * half :=
  Algebra.commutes _ x

@[expose] def ru {a b : Fin n} (h : a ≠ b) : (Cl n)ˣ where
  val := r a b
  inv := half * r a b
  val_inv := by rw [← mul_assoc, ← half_comm, mul_assoc, r_mul_self h, half_mul_two]
  inv_val := by rw [mul_assoc, r_mul_self h, half_mul_two]

@[expose] def hu : (Cl n)ˣ where
  val := half
  inv := 2
  val_inv := half_mul_two
  inv_val := two_mul_half

variable (n) in
@[expose] def monomial : Subgroup (Cl n)ˣ where
  carrier := {g | ∃ σ : Perm (Fin n), ∀ j, (g : Cl n) * v n j = v n (σ j) * g}
  mul_mem' := by
    rintro g h ⟨σ, hσ⟩ ⟨τ, hτ⟩
    refine ⟨σ * τ, fun j => ?_⟩
    rw [Units.val_mul, mul_assoc, hτ, ← mul_assoc, hσ, mul_assoc, Perm.mul_apply]
  one_mem' := ⟨1, fun j => by simp⟩
  inv_mem' := by
    rintro g ⟨σ, hσ⟩
    refine ⟨σ⁻¹, fun k => ?_⟩
    have e := hσ (σ⁻¹ k)
    rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply] at e
    calc (↑g⁻¹ : Cl n) * v n k = ↑g⁻¹ * (v n k * ↑g) * ↑g⁻¹ := by
          rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
      _ = ↑g⁻¹ * (↑g * v n (σ⁻¹ k)) * ↑g⁻¹ := by rw [e]
      _ = v n (σ⁻¹ k) * ↑g⁻¹ := by rw [Units.inv_mul_cancel_left]

def permFun (g : monomial n) : Perm (Fin n) := g.2.choose

theorem permFun_spec (g : monomial n) (j : Fin n) :
    ((g : (Cl n)ˣ) : Cl n) * v n j = v n (permFun g j) * (g : (Cl n)ˣ) :=
  g.2.choose_spec j

theorem permFun_eq (g : monomial n) {σ : Perm (Fin n)}
    (h : ∀ j, ((g : (Cl n)ˣ) : Cl n) * v n j = v n (σ j) * (g : (Cl n)ˣ)) : permFun g = σ :=
  Equiv.ext fun j => v_injective ((Units.mul_left_inj _).mp ((permFun_spec g j).symm.trans (h j)))

def perm : monomial n →* Perm (Fin n) :=
  MonoidHom.mk' permFun fun g h => permFun_eq (g * h) fun j => by
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [mul_assoc, permFun_spec h, ← mul_assoc, permFun_spec g, mul_assoc, Perm.mul_apply]

theorem perm_spec (g : monomial n) (j : Fin n) :
    ((g : (Cl n)ˣ) : Cl n) * v n j = v n (perm g j) * (g : (Cl n)ˣ) :=
  permFun_spec g j

theorem perm_eq (g : monomial n) {σ : Perm (Fin n)}
    (h : ∀ j, ((g : (Cl n)ˣ) : Cl n) * v n j = v n (σ j) * (g : (Cl n)ˣ)) : perm g = σ :=
  permFun_eq g h

theorem commute_v_of_perm_eq_one {g : monomial n} (hg : perm g = 1) (j : Fin n) :
    Commute ((g : (Cl n)ˣ) : Cl n) (v n j) := by
  have e := perm_spec g j
  rw [hg, Perm.one_apply] at e
  exact e

@[expose] def negOne : monomial n := ⟨-1, 1, fun j => by simp⟩

theorem perm_negOne : perm (negOne : monomial n) = 1 :=
  perm_eq _ fun j => by simp [negOne]

theorem negOne_ne_one : (negOne : monomial n) ≠ 1 := fun h =>
  one_ne_neg_one (congrArg (fun g : monomial n => ((g : (Cl n)ˣ) : Cl n)) h).symm

theorem dd_mul_v {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (j : Fin n) :
    half * r a b * r c d * v n j = v n ((swap a b * swap c d) j) * (half * r a b * r c d) := by
  calc half * r a b * r c d * v n j = half * (r a b * (r c d * v n j)) := by
        simp only [mul_assoc]
    _ = half * (v n (swap a b (swap c d j)) * r a b * r c d) := by
        rw [r_mul_v hcd, mul_neg, ← mul_assoc, r_mul_v hab, neg_mul, neg_neg]
    _ = v n ((swap a b * swap c d) j) * (half * r a b * r c d) := by
        rw [Perm.mul_apply]
        simp only [mul_assoc]
        rw [← mul_assoc half, half_comm (v n _), mul_assoc]

@[expose] def dd {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) : monomial n :=
  ⟨hu * ru hab * ru hcd, swap a b * swap c d, dd_mul_v hab hcd⟩

theorem coe_dd {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    (((dd hab hcd : monomial n) : (Cl n)ˣ) : Cl n) = half * r a b * r c d :=
  rfl

theorem perm_dd {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    perm (dd hab hcd) = swap a b * swap c d :=
  perm_eq _ (dd_mul_v hab hcd)

end CFSG.Alternating.Multipliers.Spin
