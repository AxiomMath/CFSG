module

public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def radFl (H : Subgroup (GL ι K)) (W W' : Submodule K (ι → K)) (hWW' : W ≤ W') :
    Subgroup ↥H where
  carrier := {g | (∀ w ∈ W, ((g : GL ι K) : Matrix ι ι K) *ᵥ w = w) ∧
    (∀ w ∈ W', ((g : GL ι K) : Matrix ι ι K) *ᵥ w - w ∈ W) ∧
    ∀ x, ((g : GL ι K) : Matrix ι ι K) *ᵥ x - x ∈ W'}
  one_mem' := ⟨fun w _ => by simp, fun w _ => by simp, fun x => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3⟩ ⟨hh1, hh2, hh3⟩
    have hmul : ∀ y, (((g * h : ↥H) : GL ι K) : Matrix ι ι K) *ᵥ y =
        ((g : GL ι K) : Matrix ι ι K) *ᵥ (((h : GL ι K) : Matrix ι ι K) *ᵥ y) := fun y => by
      rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]
    refine ⟨fun w hw => ?_, fun w hw => ?_, fun x => ?_⟩
    · rw [hmul, hh1 w hw, hg1 w hw]
    · rw [hmul]
      have h1 : ((g : GL ι K) : Matrix ι ι K) *ᵥ
          (((h : GL ι K) : Matrix ι ι K) *ᵥ w - w) =
          ((h : GL ι K) : Matrix ι ι K) *ᵥ w - w := hg1 _ (hh2 w hw)
      rw [Matrix.mulVec_sub] at h1
      have h2 : ((g : GL ι K) : Matrix ι ι K) *ᵥ (((h : GL ι K) : Matrix ι ι K) *ᵥ w) - w =
          (((h : GL ι K) : Matrix ι ι K) *ᵥ w - w) +
            (((g : GL ι K) : Matrix ι ι K) *ᵥ w - w) := by
        rw [← sub_eq_zero] at h1 ⊢
        rw [← h1]
        abel
      rw [h2]
      exact W.add_mem (hh2 w hw) (hg2 w hw)
    · rw [hmul]
      have h1 : ((g : GL ι K) : Matrix ι ι K) *ᵥ (((h : GL ι K) : Matrix ι ι K) *ᵥ x - x) -
          (((h : GL ι K) : Matrix ι ι K) *ᵥ x - x) ∈ W := hg2 _ (hh3 x)
      have h2 : ((g : GL ι K) : Matrix ι ι K) *ᵥ (((h : GL ι K) : Matrix ι ι K) *ᵥ x) - x =
          (((g : GL ι K) : Matrix ι ι K) *ᵥ (((h : GL ι K) : Matrix ι ι K) *ᵥ x - x) -
            (((h : GL ι K) : Matrix ι ι K) *ᵥ x - x)) +
          ((((h : GL ι K) : Matrix ι ι K) *ᵥ x - x) +
            (((g : GL ι K) : Matrix ι ι K) *ᵥ x - x)) := by
        rw [Matrix.mulVec_sub]
        abel
      rw [h2]
      exact W'.add_mem (hWW' h1) (W'.add_mem (hh3 x) (hg3 x))
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3⟩
    have hgi : ((g : GL ι K) : Matrix ι ι K) * (((g⁻¹ : ↥H) : GL ι K) : Matrix ι ι K) = 1 := by
      rw [Subgroup.coe_inv, Units.mul_inv]
    have hig : (((g⁻¹ : ↥H) : GL ι K) : Matrix ι ι K) * ((g : GL ι K) : Matrix ι ι K) = 1 := by
      rw [Subgroup.coe_inv, Units.inv_mul]
    have key3 : ∀ x, (((g⁻¹ : ↥H) : GL ι K) : Matrix ι ι K) *ᵥ x - x ∈ W' := by
      intro x
      set y := (((g⁻¹ : ↥H) : GL ι K) : Matrix ι ι K) *ᵥ x with hy
      have hgy : ((g : GL ι K) : Matrix ι ι K) *ᵥ y = x := by
        rw [hy, Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]
      have h1 := hg3 y
      rw [hgy] at h1
      have : y - x = -(x - y) := by abel
      rw [this]
      exact W'.neg_mem h1
    refine ⟨fun w hw => ?_, fun w hw => ?_, key3⟩
    · have h1 : (((g⁻¹ : ↥H) : GL ι K) : Matrix ι ι K) *ᵥ
          (((g : GL ι K) : Matrix ι ι K) *ᵥ w) = w := by
        rw [Matrix.mulVec_mulVec, hig, Matrix.one_mulVec]
      rwa [hg1 w hw] at h1
    · set y := (((g⁻¹ : ↥H) : GL ι K) : Matrix ι ι K) *ᵥ w with hy
      have hyW' : y ∈ W' := by
        have h1 := key3 w
        have : y = (y - w) + w := by abel
        rw [this]
        exact W'.add_mem h1 hw
      have hgy : ((g : GL ι K) : Matrix ι ι K) *ᵥ y = w := by
        rw [hy, Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]
      have h1 := hg2 y hyW'
      rw [hgy] at h1
      have : y - w = -(w - y) := by abel
      rw [this]
      exact W.neg_mem h1

theorem conj_mem_radFl {H : Subgroup (GL ι K)} {W W' : Submodule K (ι → K)} {hWW' : W ≤ W'}
    {s : ↥H}
    (hsW : ∀ w ∈ W, ((s : GL ι K) : Matrix ι ι K) *ᵥ w ∈ W)
    (hsW' : ∀ w ∈ W', ((s : GL ι K) : Matrix ι ι K) *ᵥ w ∈ W')
    (hsiW : ∀ w ∈ W, (((s⁻¹ : ↥H) : GL ι K) : Matrix ι ι K) *ᵥ w ∈ W)
    (hsiW' : ∀ w ∈ W', (((s⁻¹ : ↥H) : GL ι K) : Matrix ι ι K) *ᵥ w ∈ W')
    {g : ↥H} (hg : g ∈ radFl H W W' hWW') : s * g * s⁻¹ ∈ radFl H W W' hWW' := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hss : ((s : GL ι K) : Matrix ι ι K) * (((s⁻¹ : ↥H) : GL ι K) : Matrix ι ι K) = 1 := by
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hmul : ∀ y, (((s * g * s⁻¹ : ↥H) : GL ι K) : Matrix ι ι K) *ᵥ y =
      ((s : GL ι K) : Matrix ι ι K) *ᵥ (((g : GL ι K) : Matrix ι ι K) *ᵥ
        ((((s⁻¹ : ↥H) : GL ι K) : Matrix ι ι K) *ᵥ y)) := fun y => by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  have hsi : ∀ y, ((s : GL ι K) : Matrix ι ι K) *ᵥ
      ((((s⁻¹ : ↥H) : GL ι K) : Matrix ι ι K) *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hss, Matrix.one_mulVec]
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun x => ?_⟩
  · rw [hmul, hg1 _ (hsiW w hw), hsi]
  · rw [hmul]
    have h1 := hsW _ (hg2 _ (hsiW' w hw))
    rw [Matrix.mulVec_sub, hsi] at h1
    exact h1
  · rw [hmul]
    have h1 := hsW' _ (hg3 ((((s⁻¹ : ↥H) : GL ι K) : Matrix ι ι K) *ᵥ x))
    rw [Matrix.mulVec_sub, hsi] at h1
    exact h1

theorem pow_eq_one_of_mem_radFl {r : ℕ} [Fact r.Prime] [CharP K r] (hr3 : 3 ≤ r)
    [Nonempty ι] {H : Subgroup (GL ι K)} {W W' : Submodule K (ι → K)} {hWW' : W ≤ W'}
    {g : ↥H} (hg : g ∈ radFl H W W' hWW') : g ^ r = 1 := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  set N : Matrix ι ι K := ((g : GL ι K) : Matrix ι ι K) - 1 with hN
  have hN3 : N * N * N = 0 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    have hx : N *ᵥ x ∈ W' := by
      rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact hg3 x
    have hy : N *ᵥ (N *ᵥ x) ∈ W := by
      rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact hg2 _ hx
    have hz : N *ᵥ (N *ᵥ (N *ᵥ x)) = 0 := by
      rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec, hg1 _ hy, sub_self]
    rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz, map_zero,
      LinearMap.zero_apply]
  have hNr : N ^ r = 0 := by
    rw [show r = 3 + (r - 3) by omega, pow_add, pow_succ, pow_two, hN3, zero_mul]
  have hgN : ((g : GL ι K) : Matrix ι ι K) = 1 + N := by rw [hN]; abel
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hgN,
    add_pow_char_of_commute r (Commute.one_left N), one_pow, hNr, add_zero]
  rfl

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
