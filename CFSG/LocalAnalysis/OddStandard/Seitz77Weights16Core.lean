module

public import CFSG.GH74.KGroups.FieldGF
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.OddStandard.Seitz77

namespace Weights16

open CFSG.GH74.KGroups
open scoped Matrix

@[expose] def zeta : GF16 := GF16.ofNat' 2

theorem zeta_pow_four : zeta ^ 4 = zeta + 1 := by decide +kernel

@[expose] def lin {R : Type*} [CommSemiring R] (c : Fin 4 → R) (x : R) : R :=
  ∑ i : Fin 4, c i * x ^ 2 ^ (i : ℕ)

theorem lin_def {R : Type*} [CommSemiring R] (c : Fin 4 → R) (x : R) :
    lin c x = c 0 * x + c 1 * x ^ 2 + c 2 * x ^ 4 + c 3 * x ^ 8 := by
  simp [lin, Fin.sum_univ_four]

theorem lin_zero {R : Type*} [CommSemiring R] (x : R) : lin (0 : Fin 4 → R) x = 0 := by
  simp [lin]

theorem lin_scale {R : Type*} [CommSemiring R] (c : Fin 4 → R) (u x : R) :
    lin c (u * x) = lin (fun i => c i * u ^ 2 ^ (i : ℕ)) x := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, mul_assoc]

theorem lin_mul_left {R : Type*} [CommSemiring R] (u : R) (c : Fin 4 → R) (x : R) :
    u * lin c x = lin (fun i => u * c i) x := by
  simp only [lin, Finset.mul_sum, mul_assoc]

theorem lin_mul_right {R : Type*} [CommSemiring R] (c : Fin 4 → R) (w x : R) :
    lin c x * w = lin (fun i => c i * w) x := by
  simp only [lin, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem lin_sub {R : Type*} [CommRing R] (c d : Fin 4 → R) (x : R) :
    lin c x - lin d x = lin (fun i => c i - d i) x := by
  simp only [lin, sub_mul, Finset.sum_sub_distrib]

theorem lin_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) (c : Fin 4 → R)
    (x : R) : φ (lin c x) = lin (fun i => φ (c i)) (φ x) := by
  simp [lin, map_sum, map_mul, map_pow]

theorem add_pow_two (x y : GF16) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  revert x y; decide +kernel

theorem add_pow_four (x y : GF16) : (x + y) ^ 4 = x ^ 4 + y ^ 4 := by
  revert x y; decide +kernel

theorem add_pow_eight (x y : GF16) : (x + y) ^ 8 = x ^ 8 + y ^ 8 := by
  revert x y; decide +kernel

theorem lin_add (c : Fin 4 → GF16) (x y : GF16) : lin c (x + y) = lin c x + lin c y := by
  simp only [lin_def, add_pow_two, add_pow_four, add_pow_eight]
  ring

@[expose] def moore : Matrix (Fin 4) (Fin 4) GF16 := fun j k => (zeta ^ (j : ℕ)) ^ 2 ^ (k : ℕ)

@[expose] def mooreInv : Matrix (Fin 4) (Fin 4) GF16 :=
  fun i j => GF16.ofNat' (![![9, 4, 2, 1], ![13, 3, 4, 1], ![14, 5, 3, 1], ![11, 2, 5, 1]] i j)

theorem mooreInv_mul : mooreInv * moore = 1 := by decide +kernel

theorem moore_mul_inv : moore * mooreInv = 1 := by decide +kernel

theorem lin_basis (c : Fin 4 → GF16) (j : Fin 4) :
    lin c (zeta ^ (j : ℕ)) = (moore *ᵥ c) j := by
  simp only [lin, moore, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem lin_unique {c : Fin 4 → GF16} (h : ∀ x, lin c x = 0) : c = 0 := by
  have h1 : moore *ᵥ c = 0 := by
    funext j
    rw [← lin_basis]
    exact h _
  calc c = (mooreInv * moore) *ᵥ c := by rw [mooreInv_mul, Matrix.one_mulVec]
    _ = mooreInv *ᵥ (moore *ᵥ c) := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [h1, Matrix.mulVec_zero]

theorem sum_bits : ∀ x : GF16,
    x = ∑ j : Fin 4, if x.toNat.testBit j then zeta ^ (j : ℕ) else 0 := by
  decide +kernel

theorem eq_of_basis {f g : GF16 → GF16} (hf : ∀ x y, f (x + y) = f x + f y)
    (hg : ∀ x y, g (x + y) = g x + g y)
    (h : ∀ j : Fin 4, f (zeta ^ (j : ℕ)) = g (zeta ^ (j : ℕ))) (x : GF16) : f x = g x := by
  have key : ∀ H : GF16 →+ GF16, H x =
      ∑ j : Fin 4, if x.toNat.testBit j then H (zeta ^ (j : ℕ)) else 0 := by
    intro H
    conv_lhs => rw [sum_bits x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  have hF := key (AddMonoidHom.mk' f hf)
  have hG := key (AddMonoidHom.mk' g hg)
  simp only [AddMonoidHom.mk'_apply] at hF hG
  rw [hF, hG]
  exact Finset.sum_congr rfl fun j _ => by rw [h j]

theorem eq_lin_of_additive {f : GF16 → GF16} (hf : ∀ x y, f (x + y) = f x + f y) (x : GF16) :
    f x = lin (mooreInv *ᵥ fun j : Fin 4 => f (zeta ^ (j : ℕ))) x := by
  refine eq_of_basis hf (lin_add _) (fun j => ?_) x
  rw [lin_basis, Matrix.mulVec_mulVec, moore_mul_inv, Matrix.one_mulVec]

theorem lin_defect {R : Type*} [CommRing R] (c : Fin 4 → R) (u v x : R) :
    lin c (u * x) - v * lin c x = lin (fun i => c i * (u ^ 2 ^ (i : ℕ) - v)) x := by
  rw [lin_scale, lin_mul_left, lin_sub]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem additive_weight {r : GF16} (hr : orderOf r = 15) (a b : ℕ) {f : GF16 → GF16}
    (hf : ∀ x y, f (x + y) = f x + f y) (hrf : ∀ x, f (r ^ a * x) = r ^ b * f x) :
    ∃ c : Fin 4 → GF16, (∀ x, f x = lin c x) ∧
      ∀ i : Fin 4, c i ≠ 0 → a * 2 ^ (i : ℕ) ≡ b [MOD 15] := by
  set c : Fin 4 → GF16 := mooreInv *ᵥ fun j : Fin 4 => f (zeta ^ (j : ℕ)) with hc
  have hfc : ∀ x, f x = lin c x := eq_lin_of_additive hf
  refine ⟨c, hfc, fun i hi => ?_⟩
  have h0 : lin (fun i => c i * ((r ^ a) ^ 2 ^ (i : ℕ) - r ^ b)) = lin 0 := by
    funext x
    rw [← lin_defect, lin_zero, ← hfc, ← hfc, hrf, sub_self]
  have hu : (fun i => c i * ((r ^ a) ^ 2 ^ (i : ℕ) - r ^ b)) = 0 :=
    lin_unique fun x => (congrFun h0 x).trans (lin_zero x)
  have h1 : c i * ((r ^ a) ^ 2 ^ (i : ℕ) - r ^ b) = 0 := congrFun hu i
  have h2 : (r ^ a) ^ 2 ^ (i : ℕ) = r ^ b := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hi
    · exact sub_eq_zero.1 h
  rw [← pow_mul] at h2
  have hfin : IsOfFinOrder r := orderOf_pos_iff.1 (by rw [hr]; norm_num)
  have := hfin.pow_eq_pow_iff_modEq.1 h2
  rwa [hr] at this

end Weights16

end CFSG.OddStandard.Seitz77
