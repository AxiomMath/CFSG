module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.Basic

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section Elements

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

@[expose] noncomputable def torusDiag (c : Fˣ) : CentralExtension F b m hm heven :=
  specialInclusion F b m hm heven (diagSL F c)

@[expose] noncomputable def weylElement : CentralExtension F b m hm heven :=
  specialInclusion F b m hm heven (weyl F)

@[expose] noncomputable def torusGenerator : CentralExtension F b m hm heven :=
  (weylElement F b m hm heven)⁻¹ * cyclicGenerator F b m hm heven

@[expose] noncomputable def unipotentElement (t : F) : CentralExtension F b m hm heven :=
  specialInclusion F b m hm heven (upperSL F t)

@[expose] noncomputable def torusConstant : Fˣ := -((-b⁻¹) ^ (m / 2))

theorem torusDiag_mul (c d : Fˣ) :
    torusDiag F b m hm heven (c * d) = torusDiag F b m hm heven c * torusDiag F b m hm heven d := by
  rw [torusDiag, torusDiag, torusDiag, diagSL_mul, map_mul]

theorem torusDiag_one : torusDiag F b m hm heven 1 = 1 := by
  rw [torusDiag, diagSL_one, map_one]

theorem unipotentElement_add (s t : F) :
    unipotentElement F b m hm heven (s + t) =
      unipotentElement F b m hm heven s * unipotentElement F b m hm heven t := by
  rw [unipotentElement, unipotentElement, unipotentElement, upperSL_add, map_mul]

theorem unipotentElement_zero : unipotentElement F b m hm heven 0 = 1 := by
  rw [unipotentElement, upperSL_zero, map_one]

end Elements

section MatrixIdentities

variable (F : Type) [Field F] (b : Fˣ)

theorem SL_eq_of_val {A B : SpecialLinearGroup (Fin 2) F}
    (h : (A : Matrix (Fin 2) (Fin 2) F) = (B : Matrix (Fin 2) (Fin 2) F)) : A = B :=
  Subtype.ext h

theorem SL_mul_val (A B : SpecialLinearGroup (Fin 2) F) :
    ((A * B : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) := rfl

theorem SL_one_val :
    ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := rfl

theorem weyl_inv_val :
    (((weyl F)⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := by
  have h : weyl F * (weyl F)⁻¹ = 1 := mul_inv_cancel _
  have hm := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) h
  simp only [SL_mul_val, SL_one_val, weyl_val] at hm
  have hinv := Matrix.inv_eq_right_inv hm
  rw [← hinv, Matrix.inv_def, det_fin_two_of, adjugate_fin_two_of]
  simp

theorem beta_diagSL (c : Fˣ) : beta F b (diagSL F c) = diagSL F c⁻¹ := by
  apply SL_eq_of_val
  rw [beta_val, diagSL_val]
  change !![_, _; _, _] = !![((c⁻¹ : Fˣ) : F), 0; 0, ((c⁻¹⁻¹ : Fˣ) : F)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem weyl_inv_beta_weyl_inv :
    (weyl F)⁻¹ * beta F b (weyl F)⁻¹ = diagSL F (-b⁻¹) := by
  apply SL_eq_of_val
  have hb : (b : F) ≠ 0 := b.ne_zero
  rw [SL_mul_val, beta_val, weyl_inv_val, diagSL_val]
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals field_simp

theorem weyl_inv_diag_comm (c : Fˣ) :
    (weyl F)⁻¹ * diagSL F c⁻¹ = diagSL F c * (weyl F)⁻¹ := by
  apply SL_eq_of_val
  rw [SL_mul_val, SL_mul_val, weyl_inv_val, diagSL_val, diagSL_val,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

theorem weyl_diag_weyl_inv (c : Fˣ) :
    weyl F * diagSL F c * (weyl F)⁻¹ = diagSL F c⁻¹ := by
  apply SL_eq_of_val
  rw [SL_mul_val, SL_mul_val, weyl_inv_val, diagSL_val, diagSL_val,
    weyl_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

theorem weyl_sq : weyl F * weyl F = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F := by
  apply SL_eq_of_val
  rw [SL_mul_val, weyl_val,
    CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_matrix, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diag_upper_diag_inv (c : Fˣ) (t : F) :
    diagSL F c * upperSL F t * (diagSL F c)⁻¹ = upperSL F ((c : F) ^ 2 * t) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply SL_eq_of_val
  rw [SL_mul_val, SL_mul_val, diagSL_val, upperSL_val, upperSL_val,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals field_simp

theorem weyl_inv_lower_weyl (t : F) :
    (weyl F)⁻¹ * lowerSL F t * weyl F = upperSL F (-t) := by
  apply SL_eq_of_val
  rw [SL_mul_val, SL_mul_val, weyl_inv_val, lowerSL_val, weyl_val,
    upperSL_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

theorem beta_upperSL (t : F) : beta F b (upperSL F t) = lowerSL F (-t / b) := by
  apply SL_eq_of_val
  rw [beta_val, lowerSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperSL, neg_div]

theorem diagSL_neg_one : diagSL F (-1) = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F := by
  apply SL_eq_of_val
  rw [diagSL_val, CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end MatrixIdentities

section Relations

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

theorem one_val_eq_one : (1 : ZMod (2 * m)).val = 1 := ZMod.val_one'' (by omega)

theorem torusDiag_eq (c : Fˣ) :
    torusDiag F b m hm heven c = quotientClass F b m hm heven (diagSL F c) 0 := rfl

theorem torusGenerator_eq :
    torusGenerator F b m hm heven = quotientClass F b m hm heven (weyl F)⁻¹ 1 := by
  rw [torusGenerator, weylElement, ← map_inv, cyclicGenerator,
    specialInclusion_mul_quotientClass, mul_one]

theorem cyclicGenerator_mul_specialInclusion (X : SpecialLinearGroup (Fin 2) F) :
    cyclicGenerator F b m hm heven * specialInclusion F b m hm heven X =
      specialInclusion F b m hm heven (beta F b X) * cyclicGenerator F b m hm heven := by
  rw [← mul_inv_eq_iff_eq_mul, cyclicGenerator_conjugation]

theorem torusGenerator_mul_torusDiag (c : Fˣ) :
    torusGenerator F b m hm heven * torusDiag F b m hm heven c =
      torusDiag F b m hm heven c * torusGenerator F b m hm heven := by
  rw [torusGenerator_eq, torusDiag_eq, quotientClass_mul, quotientClass_mul, one_val_eq_one,
    pow_one, beta_diagSL, ZMod.val_zero, pow_zero, MulAut.one_apply, weyl_inv_diag_comm,
    add_zero, zero_add]

theorem torusGenerator_sq :
    torusGenerator F b m hm heven ^ 2 =
      torusDiag F b m hm heven (-b⁻¹) * cyclicGenerator F b m hm heven ^ 2 := by
  rw [pow_two, torusGenerator_eq, quotientClass_mul, one_val_eq_one, pow_one,
    weyl_inv_beta_weyl_inv, torusDiag, cyclicGenerator_pow, specialInclusion_mul_quotientClass,
    mul_one]
  congr 1
  push_cast
  ring

theorem cyclicGenerator_sq_comm (g : CentralExtension F b m hm heven) :
    cyclicGenerator F b m hm heven ^ 2 * g = g * cyclicGenerator F b m hm heven ^ 2 :=
  Subgroup.mem_center_iff.mp (cyclicGenerator_sq_mem_center F b m hm heven) g |>.symm

theorem cyclicGenerator_pow_m_comm (g : CentralExtension F b m hm heven) :
    cyclicGenerator F b m hm heven ^ m * g = g * cyclicGenerator F b m hm heven ^ m := by
  obtain ⟨k, hk⟩ := id heven
  have hpow : cyclicGenerator F b m hm heven ^ m = (cyclicGenerator F b m hm heven ^ 2) ^ k := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hpow]
  exact (Commute.pow_left (cyclicGenerator_sq_comm F b m hm heven g) k).eq

theorem torusDiag_neg_one :
    torusDiag F b m hm heven (-1) = cyclicGenerator F b m hm heven ^ m := by
  rw [torusDiag, diagSL_neg_one, cyclicGenerator_pow_m]

theorem torusDiag_pow (c : Fˣ) (k : ℕ) :
    torusDiag F b m hm heven (c ^ k) = torusDiag F b m hm heven c ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, torusDiag_one]
  | succ k ih => rw [pow_succ, pow_succ, torusDiag_mul, ih]

theorem torusGenerator_pow_m :
    torusGenerator F b m hm heven ^ m = torusDiag F b m hm heven (torusConstant F b m) := by
  obtain ⟨k, hk⟩ := id heven
  have hdiv : m / 2 = k := by omega
  have hpow : torusGenerator F b m hm heven ^ m = (torusGenerator F b m hm heven ^ 2) ^ k := by
    rw [← pow_mul]
    congr 1
    omega
  have hupow : (cyclicGenerator F b m hm heven ^ 2) ^ k = cyclicGenerator F b m hm heven ^ m := by
    rw [← pow_mul]
    congr 1
    omega
  have hcomm : Commute (torusDiag F b m hm heven (-b⁻¹)) (cyclicGenerator F b m hm heven ^ 2) :=
    (cyclicGenerator_sq_comm F b m hm heven _).symm
  rw [hpow, torusGenerator_sq, hcomm.mul_pow, hupow, ← torusDiag_neg_one F b m hm heven,
    ← torusDiag_pow, ← torusDiag_mul, torusConstant, hdiv, mul_neg_one]

theorem weylElement_sq :
    weylElement F b m hm heven ^ 2 = cyclicGenerator F b m hm heven ^ m := by
  rw [pow_two, weylElement, ← map_mul, weyl_sq, cyclicGenerator_pow_m]

theorem weylElement_conj_torusDiag (c : Fˣ) :
    weylElement F b m hm heven * torusDiag F b m hm heven c * (weylElement F b m hm heven)⁻¹ =
      torusDiag F b m hm heven c⁻¹ := by
  rw [weylElement, torusDiag, torusDiag, ← map_mul, ← map_inv, ← map_mul, weyl_diag_weyl_inv]

theorem cyclicGenerator_pow_two_m :
    cyclicGenerator F b m hm heven ^ (2 * m) = 1 := by
  rw [cyclicGenerator_pow, ZMod.natCast_self]
  rfl

theorem weylElement_inv :
    (weylElement F b m hm heven)⁻¹ =
      cyclicGenerator F b m hm heven ^ m * weylElement F b m hm heven := by
  have hxc := cyclicGenerator_pow_m_comm F b m hm heven (weylElement F b m hm heven)
  rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← hxc, mul_assoc, ← pow_two, weylElement_sq, ← pow_add,
    ← two_mul, cyclicGenerator_pow_two_m]

theorem weylElement_conj_torusGenerator :
    weylElement F b m hm heven * torusGenerator F b m hm heven * (weylElement F b m hm heven)⁻¹ =
      cyclicGenerator F b m hm heven ^ 2 * cyclicGenerator F b m hm heven ^ m *
        (torusGenerator F b m hm heven)⁻¹ := by
  have hxc := cyclicGenerator_pow_m_comm F b m hm heven
  rw [torusGenerator, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left, weylElement_inv]
  calc cyclicGenerator F b m hm heven *
        (cyclicGenerator F b m hm heven ^ m * weylElement F b m hm heven)
      = cyclicGenerator F b m hm heven * cyclicGenerator F b m hm heven ^ m *
          weylElement F b m hm heven := by group
    _ = cyclicGenerator F b m hm heven ^ 2 * cyclicGenerator F b m hm heven ^ m *
          ((cyclicGenerator F b m hm heven)⁻¹ * weylElement F b m hm heven) := by
      rw [pow_two, mul_assoc, mul_assoc, ← mul_assoc (cyclicGenerator F b m hm heven ^ m),
        hxc (cyclicGenerator F b m hm heven)⁻¹]
      group

theorem weylElement_inv_conj (g : CentralExtension F b m hm heven) :
    (weylElement F b m hm heven)⁻¹ * g * weylElement F b m hm heven =
      weylElement F b m hm heven * g * (weylElement F b m hm heven)⁻¹ := by
  have hxc := cyclicGenerator_pow_m_comm F b m hm heven
  rw [weylElement_inv, ← mul_assoc (weylElement F b m hm heven * g),
    ← hxc (weylElement F b m hm heven * g)]
  simp only [mul_assoc]

theorem torusDiag_conj_unipotent (c : Fˣ) (t : F) :
    torusDiag F b m hm heven c * unipotentElement F b m hm heven t *
      (torusDiag F b m hm heven c)⁻¹ = unipotentElement F b m hm heven ((c : F) ^ 2 * t) := by
  rw [torusDiag, unipotentElement, unipotentElement, ← map_mul, ← map_inv, ← map_mul,
    diag_upper_diag_inv]

theorem torusGenerator_conj_unipotent (t : F) :
    torusGenerator F b m hm heven * unipotentElement F b m hm heven t *
      (torusGenerator F b m hm heven)⁻¹ = unipotentElement F b m hm heven (t / b) := by
  rw [torusGenerator, _root_.mul_inv_rev, inv_inv]
  calc (weylElement F b m hm heven)⁻¹ * cyclicGenerator F b m hm heven *
        unipotentElement F b m hm heven t *
        ((cyclicGenerator F b m hm heven)⁻¹ * weylElement F b m hm heven)
      = (weylElement F b m hm heven)⁻¹ * (cyclicGenerator F b m hm heven *
          unipotentElement F b m hm heven t * (cyclicGenerator F b m hm heven)⁻¹) *
          weylElement F b m hm heven := by group
    _ = _ := by
      rw [unipotentElement, cyclicGenerator_conjugation, beta_upperSL, weylElement, ← map_inv,
        ← map_mul, ← map_mul, weyl_inv_lower_weyl, unipotentElement, neg_div, neg_neg]

end Relations

end CFSG.Wreathed.CentralSL2
