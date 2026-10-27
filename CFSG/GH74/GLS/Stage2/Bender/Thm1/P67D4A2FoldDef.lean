module

public import CFSG.GH74.GLS.SP.GlueN

public section

open CFSG.GH74.BNPair
open scoped Pointwise

namespace CFSG.GH74.GLS.SP

variable {X : Type*} [Group X]

@[expose] def foldFix (φ : X ≃* X) : Subgroup X where
  carrier := {x | φ x = x}
  one_mem' := map_one φ
  mul_mem' := fun {a b} (ha : φ a = a) (hb : φ b = b) => by
    show φ (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := fun {a} (ha : φ a = a) => by
    show φ a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_foldFix {φ : X ≃* X} {x : X} : x ∈ foldFix φ ↔ φ x = x := Iff.rfl

@[expose] def foldIdx (k : ℤ) : ℤ := if 0 < k then 2 * k - 1 else 2 * k + 1

@[expose] def foldRoot (φ : X ≃* X) (root : ℤ → Subgroup X) (k : ℤ) : Subgroup X :=
  root (foldIdx k) ⊓ foldFix φ

@[expose] def foldLo (i : ℤ) : ℤ := max 1 (2 * i - 2)

@[expose] def foldHi (j : ℤ) : ℤ := min 6 (2 * j)

theorem mem_foldRoot {φ : X ≃* X} {root : ℤ → Subgroup X} {k : ℤ} {x : X} :
    x ∈ foldRoot φ root k ↔ x ∈ root (foldIdx k) ∧ φ x = x :=
  Iff.rfl

theorem foldIdx_of_pos {k : ℤ} (hk : 0 < k) : foldIdx k = 2 * k - 1 := ite_eq_left hk

theorem foldIdx_of_neg {k : ℤ} (hk : k < 0) : foldIdx k = 2 * k + 1 :=
  ite_eq_right (by omega)

theorem foldIdx_odd {k : ℤ} (hk : k ≠ 0) : foldIdx k % 2 ≠ 0 := by
  rcases lt_or_gt_of_ne hk with h | h
  · rw [foldIdx_of_neg h]; omega
  · rw [foldIdx_of_pos h]; omega

theorem isRoot_foldIdx {k : ℤ} (hk : IsRoot 3 k) : IsRoot 6 (foldIdx k) := by
  obtain ⟨h0, h3⟩ := hk
  rcases lt_or_gt_of_ne h0 with h | h
  · rw [foldIdx_of_neg h]; refine ⟨by omega, by omega⟩
  · rw [foldIdx_of_pos h]; refine ⟨by omega, by omega⟩

variable {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}

structure FoldData (R : RGD2 6 H r₁ r₂ U root) (φ : X ≃* X) : Prop where
  mem_H : ∀ h ∈ H, φ h ∈ H
  mem_root : ∀ k, IsRoot 6 k → ∀ x ∈ root k, φ x ∈ root k
  r₁_mem : r₁⁻¹ * φ r₁ ∈ H
  r₂_mem : r₂⁻¹ * φ r₂ ∈ H
  even_fix : ∀ k, IsRoot 6 k → k % 2 = 0 → ∀ x ∈ root k, φ x = x → x = 1
  odd_fix : ∀ k, IsRoot 6 k → k % 2 ≠ 0 → ∃ x ∈ root k, x ≠ 1 ∧ φ x = x

namespace RGD2

variable {n : ℕ} (R : RGD2 n H r₁ r₂ U root)

include R in
theorem actsPos_H_mul {h m : X} (hh : h ∈ H) {f : ℤ → ℤ} (hm : ActsPos n root m f) :
    ActsPos n root (h * m) f :=
  (R.actsPos_of_mem_H hh).mul hm

include R in
theorem actsPos_mul_H {h m : X} (hh : h ∈ H) {f : ℤ → ℤ} (hm : ActsPos n root m f) :
    ActsPos n root (m * h) f :=
  hm.mul (R.actsPos_of_mem_H hh)

include R in
theorem actsPos_alpha :
    ActsPos n root (r₂ * r₁ * r₂⁻¹) (fun q => (n : ℤ) - 4 - q) := by
  have h2 := R.actsPos_r₂
  have h1 := R.actsPos_r₁
  have h2' := R.actsPos_inv_of_sq R.sq₂ R.actsPos_r₂
  refine ((h2.mul h1).mul h2').congr (fun q => ?_)
  ring

include R in
theorem actsPos_alpha_inv :
    ActsPos n root (r₂ * r₁⁻¹ * r₂⁻¹) (fun q => (n : ℤ) - 4 - q) := by
  have h2 := R.actsPos_r₂
  have h1 := R.actsPos_inv_of_sq R.sq₁ R.actsPos_r₁
  have h2' := R.actsPos_inv_of_sq R.sq₂ R.actsPos_r₂
  refine ((h2.mul h1).mul h2').congr (fun q => ?_)
  ring

include R in
theorem r_alpha_mem_N : r₂ * r₁ * r₂⁻¹ ∈ R.N :=
  R.N.mul_mem (R.N.mul_mem R.r₂_mem_N R.r₁_mem_N) (R.N.inv_mem R.r₂_mem_N)

end RGD2

end CFSG.GH74.GLS.SP
