module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

public noncomputable section

namespace CFSG.LieType.Chevalley

open Matrix

variable {K : Type*} [Field K]

abbrev SL2 (K : Type*) [Field K] := Matrix.SpecialLinearGroup (Fin 2) K

@[expose] def uSL (s : K) : SL2 K := ⟨!![1, s; 0, 1], by simp [det_fin_two]⟩

@[expose] def vSL (s : K) : SL2 K := ⟨!![1, 0; s, 1], by simp [det_fin_two]⟩

@[expose] def HSL (t : Kˣ) : SL2 K := ⟨!![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)], by simp [det_fin_two]⟩

@[expose] def WSL : SL2 K := ⟨!![0, 1; -1, 0], by simp [det_fin_two]⟩

theorem coe_uSL (s : K) : ((uSL s : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![1, s; 0, 1] := rfl

theorem coe_vSL (s : K) : ((vSL s : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; s, 1] := rfl

theorem coe_HSL (t : Kˣ) :
    ((HSL t : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)] := rfl

theorem coe_WSL : ((WSL : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl

theorem det_SL2 (g : SL2 K) :
    (g : Matrix (Fin 2) (Fin 2) K) 0 0 * (g : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) K) 0 1 * (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
  have := g.2
  rwa [det_fin_two] at this

theorem SL2_apply_zero_zero_ne_zero {g : SL2 K} (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := fun ha => by
  have := det_SL2 g
  rw [ha, hc] at this
  simp at this

theorem SL2_ext {g g' : SL2 K}
    (h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = (g' : Matrix (Fin 2) (Fin 2) K) 0 0)
    (h01 : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = (g' : Matrix (Fin 2) (Fin 2) K) 0 1)
    (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = (g' : Matrix (Fin 2) (Fin 2) K) 1 0)
    (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = (g' : Matrix (Fin 2) (Fin 2) K) 1 1) : g = g' := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem eq_HSL_mul_uSL {g : SL2 K} (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    g = HSL (Units.mk0 _ (SL2_apply_zero_zero_ne_zero hc)) *
      uSL ((g : Matrix (Fin 2) (Fin 2) K) 0 1 / (g : Matrix (Fin 2) (Fin 2) K) 0 0) := by
  have ha := SL2_apply_zero_zero_ne_zero hc
  have hdet := det_SL2 g
  rw [hc, mul_zero, sub_zero] at hdet
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_HSL, coe_uSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hc]
  · field_simp
  · field_simp
    linear_combination hdet

theorem eq_uSL_mul_HSL_mul_WSL_mul_uSL {g : SL2 K}
    (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    g = uSL ((g : Matrix (Fin 2) (Fin 2) K) 0 0 / (g : Matrix (Fin 2) (Fin 2) K) 1 0) *
      HSL (Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
        (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc)) * WSL *
      uSL ((g : Matrix (Fin 2) (Fin 2) K) 1 1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  have hdet := det_SL2 g
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_HSL, coe_uSL, coe_WSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp
  · field_simp
    linear_combination -hdet
  · field_simp
  · field_simp

section Gauss

variable {A : Type*} [Group A] (x : Multiplicative K →* A) (h : Kˣ →* A) (n : A)

open _root_.Classical in
@[expose] def gaussFun (g : SL2 K) : A :=
  if hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 then
    h (Units.mk0 _ (SL2_apply_zero_zero_ne_zero hc)) *
      x (Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K) 0 1 /
        (g : Matrix (Fin 2) (Fin 2) K) 0 0))
  else
    x (Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K) 0 0 /
        (g : Matrix (Fin 2) (Fin 2) K) 1 0)) *
      h (Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
        (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc)) * n *
      x (Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K) 1 1 /
        (g : Matrix (Fin 2) (Fin 2) K) 1 0))

variable {x h n}

theorem gaussFun_of_eq {g : SL2 K} (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) {a : Kˣ}
    (ha : (a : K) = (g : Matrix (Fin 2) (Fin 2) K) 0 0) {b : K}
    (hb : b = (g : Matrix (Fin 2) (Fin 2) K) 0 1 / (g : Matrix (Fin 2) (Fin 2) K) 0 0) :
    gaussFun x h n g = h a * x (Multiplicative.ofAdd b) := by
  rw [gaussFun, dite_eq_left hc, hb,
    show Units.mk0 _ (SL2_apply_zero_zero_ne_zero hc) = a from Units.ext ha.symm]

theorem gaussFun_of_ne {g : SL2 K} (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) {a d : K}
    (ha : a = (g : Matrix (Fin 2) (Fin 2) K) 0 0 / (g : Matrix (Fin 2) (Fin 2) K) 1 0) {t : Kˣ}
    (ht : (t : K) = -1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
    (hd : d = (g : Matrix (Fin 2) (Fin 2) K) 1 1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0) :
    gaussFun x h n g =
      x (Multiplicative.ofAdd a) * h t * n * x (Multiplicative.ofAdd d) := by
  rw [gaussFun, dite_eq_right hc, ha, hd,
    show Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
      (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc) = t from Units.ext ht.symm]

structure GaussRel (x : Multiplicative K →* A) (h : Kˣ →* A) (n : A) : Prop where
  conj_x : ∀ (t : Kˣ) (s : K), h t * x (Multiplicative.ofAdd s) * (h t)⁻¹ =
    x (Multiplicative.ofAdd ((t : K) ^ 2 * s))
  sq_n : n ^ 2 = h (-1)
  conj_h : ∀ t : Kˣ, n * h t * n⁻¹ = h t⁻¹
  gauss : ∀ (s : K) (hs : s ≠ 0), n * x (Multiplicative.ofAdd s) * n =
    x (Multiplicative.ofAdd (-s⁻¹)) * h (Units.mk0 (-s⁻¹) (neg_ne_zero.2 (inv_ne_zero hs))) * n *
      x (Multiplicative.ofAdd (-s⁻¹))

theorem gaussFun_one : gaussFun x h n (1 : SL2 K) = 1 := by
  rw [gaussFun_of_eq (a := 1) (b := 0) (by simp) (by simp) (by simp)]
  simp

variable (hR : GaussRel x h n)
include hR

theorem GaussRel.h_mul_x (t : Kˣ) (s : K) :
    h t * x (Multiplicative.ofAdd s) = x (Multiplicative.ofAdd ((t : K) ^ 2 * s)) * h t := by
  rw [← hR.conj_x, inv_mul_cancel_right]

theorem GaussRel.x_mul_h (t : Kˣ) (s : K) :
    x (Multiplicative.ofAdd s) * h t =
      h t * x (Multiplicative.ofAdd (((t : K)⁻¹) ^ 2 * s)) := by
  rw [hR.h_mul_x]
  congr 3
  have ht := t.ne_zero
  field_simp

theorem GaussRel.n_mul_h (t : Kˣ) : n * h t = h t⁻¹ * n := by
  rw [← hR.conj_h, inv_mul_cancel_right]

theorem gaussFun_uSL_mul (s : K) (g : SL2 K) :
    gaussFun x h n (uSL s * g) = x (Multiplicative.ofAdd s) * gaussFun x h n g := by
  have hdet := det_SL2 g
  have e00 : ((uSL s * g : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      (g : Matrix (Fin 2) (Fin 2) K) 0 0 + s * (g : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    simp [coe_uSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : ((uSL s * g : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      (g : Matrix (Fin 2) (Fin 2) K) 0 1 + s * (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    simp [coe_uSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : ((uSL s * g : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    simp [coe_uSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : ((uSL s * g : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    simp [coe_uSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · have ha := SL2_apply_zero_zero_ne_zero hc
    rw [hc, mul_zero, sub_zero] at hdet
    have hd : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = ((g : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹ :=
      eq_inv_of_mul_eq_one_right hdet
    rw [gaussFun_of_eq (g := uSL s * g) (by rw [e10]; exact hc) (a := Units.mk0 _ ha)
        (by rw [e00, hc, mul_zero, add_zero]; rfl)
        (b := (g : Matrix (Fin 2) (Fin 2) K) 0 1 / (g : Matrix (Fin 2) (Fin 2) K) 0 0 +
          ((g : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹ ^ 2 * s)
        (by
          rw [e00, e01, hc, mul_zero, add_zero, hd]
          field_simp),
      gaussFun_of_eq hc (a := Units.mk0 _ ha) rfl rfl, ← mul_assoc, hR.x_mul_h, mul_assoc,
      ← map_mul, ← ofAdd_add, Units.val_mk0, add_comm]
  · rw [gaussFun_of_ne (g := uSL s * g) (by rw [e10]; exact hc)
        (a := s + (g : Matrix (Fin 2) (Fin 2) K) 0 0 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
        (by rw [e00, e10]; field_simp; ring)
        (t := Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
          (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc)) (by rw [e10]; rfl)
        (d := (g : Matrix (Fin 2) (Fin 2) K) 1 1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
        (by rw [e10, e11]),
      gaussFun_of_ne hc rfl (t := Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
        (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc)) rfl rfl, ofAdd_add, map_mul]
    simp only [mul_assoc]

theorem gaussFun_HSL_mul (t : Kˣ) (g : SL2 K) :
    gaussFun x h n (HSL t * g) = h t * gaussFun x h n g := by
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  have e00 : ((HSL t * g : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      t * (g : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    simp [coe_HSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : ((HSL t * g : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      t * (g : Matrix (Fin 2) (Fin 2) K) 0 1 := by
    simp [coe_HSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : ((HSL t * g : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      (t : K)⁻¹ * (g : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    simp [coe_HSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : ((HSL t * g : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      (t : K)⁻¹ * (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    simp [coe_HSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · have ha := SL2_apply_zero_zero_ne_zero hc
    rw [gaussFun_of_eq (g := HSL t * g) (by rw [e10, hc, mul_zero]) (a := t * Units.mk0 _ ha)
        (by rw [e00]; rfl)
        (b := (g : Matrix (Fin 2) (Fin 2) K) 0 1 / (g : Matrix (Fin 2) (Fin 2) K) 0 0)
        (by rw [e00, e01]; field_simp),
      gaussFun_of_eq hc (a := Units.mk0 _ ha) rfl rfl, map_mul, mul_assoc]
  · have hc' : (t : K)⁻¹ * (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 :=
      mul_ne_zero (inv_ne_zero ht0) hc
    rw [gaussFun_of_ne (g := HSL t * g) (by rw [e10]; exact hc')
        (a := (t : K) ^ 2 *
          ((g : Matrix (Fin 2) (Fin 2) K) 0 0 / (g : Matrix (Fin 2) (Fin 2) K) 1 0))
        (by rw [e00, e10]; field_simp)
        (t := t * Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
          (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc))
        (by rw [e10, Units.val_mul, Units.val_mk0]; field_simp)
        (d := (g : Matrix (Fin 2) (Fin 2) K) 1 1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
        (by rw [e10, e11]; field_simp),
      gaussFun_of_ne hc rfl (t := Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
        (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc)) rfl rfl, map_mul h,
      ← mul_assoc (x _) (h t), ← hR.h_mul_x]
    simp only [mul_assoc]

theorem gaussFun_WSL_mul (g : SL2 K) : gaussFun x h n (WSL * g) = n * gaussFun x h n g := by
  have hdet := det_SL2 g
  have e00 : ((WSL * g : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    simp [coe_WSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : ((WSL * g : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    simp [coe_WSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : ((WSL * g : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      -(g : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    simp [coe_WSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : ((WSL * g : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      -(g : Matrix (Fin 2) (Fin 2) K) 0 1 := by
    simp [coe_WSL, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · have ha := SL2_apply_zero_zero_ne_zero hc
    rw [gaussFun_of_ne (g := WSL * g) (by rw [e10]; exact neg_ne_zero.2 ha) (a := 0)
        (by rw [e00, e10, hc, zero_div]) (t := (Units.mk0 _ ha)⁻¹)
        (by rw [e10, Units.val_inv_eq_inv_val, Units.val_mk0, neg_div_neg_eq, one_div])
        (d := (g : Matrix (Fin 2) (Fin 2) K) 0 1 / (g : Matrix (Fin 2) (Fin 2) K) 0 0)
        (by rw [e10, e11, neg_div_neg_eq]),
      gaussFun_of_eq hc (a := Units.mk0 _ ha) rfl rfl, ofAdd_zero, map_one, one_mul,
      ← mul_assoc n, hR.n_mul_h]
  · by_cases ha : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 0
    · rw [gaussFun_of_eq (g := WSL * g) (by rw [e10, ha, neg_zero]) (a := Units.mk0 _ hc)
          (by rw [e00]; rfl)
          (b := (g : Matrix (Fin 2) (Fin 2) K) 1 1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
          (by rw [e00, e01]),
        gaussFun_of_ne hc (a := 0) (by rw [ha, zero_div])
          (t := Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
            (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc)) rfl rfl,
        ofAdd_zero, map_one, one_mul, ← mul_assoc n, ← mul_assoc n, hR.n_mul_h,
        mul_assoc _ n n, ← sq, hR.sq_n, ← map_mul]
      congr 2
      refine Units.ext ?_
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_neg,
        Units.val_one]
      field_simp
    · set σ := (g : Matrix (Fin 2) (Fin 2) K) 0 0 / (g : Matrix (Fin 2) (Fin 2) K) 1 0 with hσdef
      have hσ : σ ≠ 0 := div_ne_zero ha hc
      set u1 : Kˣ := Units.mk0 (-σ⁻¹) (neg_ne_zero.2 (inv_ne_zero hσ))
      set u2 : Kˣ := Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
        (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc)
      set u3 : Kˣ := Units.mk0 (-(g : Matrix (Fin 2) (Fin 2) K) 1 0) (neg_ne_zero.2 hc)
      have hu23 : u2 = u3⁻¹ := Units.ext (by
        simp only [u2, u3, Units.val_inv_eq_inv_val, Units.val_mk0]
        field_simp)
      have hconj : n⁻¹ * h u2 * n = h u3 := by
        rw [hu23, ← hR.conj_h u3]
        group
      have hw : u1 * u3⁻¹ = (Units.mk0 _ ha)⁻¹ := Units.ext (by
        simp only [u1, u3, σ, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
        field_simp)
      have hp : ((u3 : K)⁻¹) ^ 2 * -σ⁻¹ +
          (g : Matrix (Fin 2) (Fin 2) K) 1 1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0 =
          (g : Matrix (Fin 2) (Fin 2) K) 0 1 / (g : Matrix (Fin 2) (Fin 2) K) 0 0 := by
        simp only [u3, σ, Units.val_mk0]
        field_simp
        linear_combination hdet
      rw [gaussFun_of_ne (g := WSL * g) (by rw [e10]; exact neg_ne_zero.2 ha) (a := -σ⁻¹)
          (by rw [e00, e10, hσdef]; field_simp) (t := (Units.mk0 _ ha)⁻¹)
          (by rw [e10, Units.val_inv_eq_inv_val, Units.val_mk0, neg_div_neg_eq, one_div])
          (d := (g : Matrix (Fin 2) (Fin 2) K) 0 1 / (g : Matrix (Fin 2) (Fin 2) K) 0 0)
          (by rw [e10, e11, neg_div_neg_eq]),
        gaussFun_of_ne hc rfl (t := u2) rfl rfl]
      calc x (Multiplicative.ofAdd (-σ⁻¹)) * h (Units.mk0 _ ha)⁻¹ * n *
            x (Multiplicative.ofAdd
              ((g : Matrix (Fin 2) (Fin 2) K) 0 1 / (g : Matrix (Fin 2) (Fin 2) K) 0 0))
          = x (Multiplicative.ofAdd (-σ⁻¹)) * h u1 * (h u3⁻¹ * n) *
            x (Multiplicative.ofAdd (((u3 : K)⁻¹) ^ 2 * -σ⁻¹ +
              (g : Matrix (Fin 2) (Fin 2) K) 1 1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)) := by
            rw [hp, ← hw, map_mul]
            group
        _ = x (Multiplicative.ofAdd (-σ⁻¹)) * h u1 * n *
            (h u3 * x (Multiplicative.ofAdd (((u3 : K)⁻¹) ^ 2 * -σ⁻¹))) *
            x (Multiplicative.ofAdd
              ((g : Matrix (Fin 2) (Fin 2) K) 1 1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)) := by
            rw [← hR.n_mul_h, ofAdd_add, map_mul]
            group
        _ = (x (Multiplicative.ofAdd (-σ⁻¹)) * h u1 * n * x (Multiplicative.ofAdd (-σ⁻¹))) *
            h u3 * x (Multiplicative.ofAdd
              ((g : Matrix (Fin 2) (Fin 2) K) 1 1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)) := by
            rw [← hR.x_mul_h]
            group
        _ = (n * x (Multiplicative.ofAdd σ) * n) * (n⁻¹ * h u2 * n) *
            x (Multiplicative.ofAdd
              ((g : Matrix (Fin 2) (Fin 2) K) 1 1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)) := by
            rw [hR.gauss σ hσ, hconj]
        _ = _ := by simp only [mul_assoc, mul_inv_cancel_left, hσdef]

end Gauss

theorem SL2_induction {p : SL2 K → Prop} (hmul : ∀ g g', p g → p g' → p (g * g'))
    (hu : ∀ s, p (uSL s)) (hH : ∀ t, p (HSL t)) (hW : p WSL) (g : SL2 K) : p g := by
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · rw [eq_HSL_mul_uSL hc]
    exact hmul _ _ (hH _) (hu _)
  · rw [eq_uSL_mul_HSL_mul_WSL_mul_uSL hc]
    exact hmul _ _ (hmul _ _ (hmul _ _ (hu _) (hH _)) hW) (hu _)

theorem vSL_eq (s : K) : vSL s = WSL * uSL (-s) * WSL⁻¹ := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_vSL, coe_uSL, coe_WSL, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]

theorem exceptional_rank_one_Gaussian_realization {A : Type*} [Group A]
    (x : Multiplicative K →* A) (h : Kˣ →* A) (n : A)
    (hx : ∀ (t : Kˣ) (s : K), h t * x (Multiplicative.ofAdd s) * (h t)⁻¹ =
      x (Multiplicative.ofAdd ((t : K) ^ 2 * s)))
    (hn2 : n ^ 2 = h (-1)) (hnh : ∀ t : Kˣ, n * h t * n⁻¹ = h t⁻¹)
    (hgauss : ∀ (s : K) (hs : s ≠ 0), n * x (Multiplicative.ofAdd s) * n =
      x (Multiplicative.ofAdd (-s⁻¹)) * h (Units.mk0 (-s⁻¹) (neg_ne_zero.2 (inv_ne_zero hs))) *
        n * x (Multiplicative.ofAdd (-s⁻¹))) :
    ∃ ρ : SL2 K →* A,
      ((∀ s, ρ (uSL s) = x (Multiplicative.ofAdd s)) ∧ (∀ t, ρ (HSL t) = h t) ∧ ρ WSL = n) ∧
      (∀ ρ' : SL2 K →* A, (∀ s, ρ' (uSL s) = x (Multiplicative.ofAdd s)) →
        (∀ t, ρ' (HSL t) = h t) → ρ' WSL = n → ρ' = ρ) ∧
      ρ.range = Subgroup.closure (Set.range x ∪ Set.range h ∪ {n}) ∧
      Subgroup.closure (Set.range x ∪ Set.range h ∪ {n}) =
        Subgroup.closure (Set.range x ∪ {n}) ∧
      (∀ s, ρ (vSL s) = n * x (Multiplicative.ofAdd (-s)) * n⁻¹) ∧
      (∀ (g : SL2 K) (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0),
        ρ g = h (Units.mk0 _ (SL2_apply_zero_zero_ne_zero hc)) *
          x (Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K) 0 1 /
            (g : Matrix (Fin 2) (Fin 2) K) 0 0))) ∧
      ∀ (g : SL2 K) (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0),
        ρ g = x (Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K) 0 0 /
            (g : Matrix (Fin 2) (Fin 2) K) 1 0)) *
          h (Units.mk0 (-1 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)
            (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc)) * n *
          x (Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K) 1 1 /
            (g : Matrix (Fin 2) (Fin 2) K) 1 0)) := by
  have hR : GaussRel x h n := ⟨hx, hn2, hnh, hgauss⟩
  have hu1 : ∀ s, gaussFun x h n (uSL s) = x (Multiplicative.ofAdd s) := fun s => by
    simpa [gaussFun_one] using gaussFun_uSL_mul hR s 1
  have hH1 : ∀ t, gaussFun x h n (HSL t) = h t := fun t => by
    simpa [gaussFun_one] using gaussFun_HSL_mul hR t 1
  have hW1 : gaussFun x h n WSL = n := by
    simpa [gaussFun_one] using gaussFun_WSL_mul hR 1
  have hmul : ∀ g g', gaussFun x h n (g * g') = gaussFun x h n g * gaussFun x h n g' := by
    intro g
    induction g using SL2_induction with
    | hmul a b ha hb =>
      intro g'
      rw [mul_assoc, ha, hb, ha, mul_assoc]
    | hu s => exact fun g' => by rw [gaussFun_uSL_mul hR, hu1]
    | hH t => exact fun g' => by rw [gaussFun_HSL_mul hR, hH1]
    | hW => exact fun g' => by rw [gaussFun_WSL_mul hR, hW1]
  let ρ : SL2 K →* A :=
    { toFun := gaussFun x h n
      map_one' := gaussFun_one
      map_mul' := hmul }
  have hS : Set.range x ∪ Set.range h ∪ {n} ⊆ ρ.range := by
    rintro _ ((⟨s, rfl⟩ | ⟨t, rfl⟩) | rfl)
    · exact ⟨uSL s.toAdd, hu1 _⟩
    · exact ⟨HSL t, hH1 t⟩
    · exact ⟨WSL, hW1⟩
  refine ⟨ρ, ⟨hu1, hH1, hW1⟩, fun ρ' hu' hH' hW' => ?_, ?_, ?_, fun s => ?_,
    fun g hc => gaussFun_of_eq hc rfl rfl, fun g hc => gaussFun_of_ne hc rfl rfl rfl⟩
  · ext g
    induction g using SL2_induction with
    | hmul a b ha hb => rw [map_mul, map_mul, ha, hb]
    | hu s => exact (hu' s).trans (hu1 s).symm
    | hH t => exact (hH' t).trans (hH1 t).symm
    | hW => exact hW'.trans hW1.symm
  · refine le_antisymm ?_ ((Subgroup.closure_le _).2 hS)
    rintro _ ⟨g, rfl⟩
    induction g using SL2_induction with
    | hmul a b ha hb => rw [map_mul]; exact mul_mem ha hb
    | hu s => exact Subgroup.subset_closure (Or.inl (Or.inl ⟨_, (hu1 s).symm⟩))
    | hH t => exact Subgroup.subset_closure (Or.inl (Or.inr ⟨_, (hH1 t).symm⟩))
    | hW => exact Subgroup.subset_closure (Or.inr hW1)
  · refine le_antisymm ((Subgroup.closure_le _).2 ?_)
      (Subgroup.closure_mono (Set.union_subset_union_left _ Set.subset_union_left))
    rintro _ ((⟨s, rfl⟩ | ⟨t, rfl⟩) | rfl)
    · exact Subgroup.subset_closure (Or.inl ⟨s, rfl⟩)
    ·
      have hs : -((t : K)⁻¹) ≠ 0 := neg_ne_zero.2 (inv_ne_zero t.ne_zero)
      have key := hgauss (-((t : K)⁻¹)) hs
      have ht : Units.mk0 (-(-((t : K)⁻¹))⁻¹) (neg_ne_zero.2 (inv_ne_zero hs)) = t :=
        Units.ext (by simp)
      rw [ht] at key
      have hmem : ∀ c : K, x (Multiplicative.ofAdd c) ∈
          Subgroup.closure (Set.range x ∪ {n}) := fun c =>
        Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
      have hn : n ∈ Subgroup.closure (Set.range x ∪ {n}) := Subgroup.subset_closure (Or.inr rfl)
      have heq : h t = (x (Multiplicative.ofAdd (-(-((t : K)⁻¹))⁻¹)))⁻¹ *
          (n * x (Multiplicative.ofAdd (-((t : K)⁻¹))) * n) *
          (x (Multiplicative.ofAdd (-(-((t : K)⁻¹))⁻¹)))⁻¹ * n⁻¹ := by
        rw [key]
        group
      rw [heq]
      exact mul_mem (mul_mem (mul_mem (inv_mem (hmem _)) (mul_mem (mul_mem hn (hmem _)) hn))
        (inv_mem (hmem _))) (inv_mem hn)
    · exact Subgroup.subset_closure (Or.inr rfl)
  · change gaussFun x h n (vSL s) = _
    rw [vSL_eq, hmul, hmul, hW1, hu1,
      show gaussFun x h n WSL⁻¹ = n⁻¹ from (map_inv ρ WSL).trans (congrArg _ hW1)]

end CFSG.LieType.Chevalley
