module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

open Matrix

namespace CFSG.LinearAlgebra

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mulVec_inv_mulVec (g : GL ι K) (x : ι → K) :
    (g : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem inv_mulVec_mulVec (g : GL ι K) (x : ι → K) :
    ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

@[expose] def unipotentRadical (W : Submodule K (ι → K)) : Subgroup (GL ι K) where
  carrier := {g | (∀ x, (g : Matrix ι ι K) *ᵥ x - x ∈ W) ∧ ∀ x ∈ W, (g : Matrix ι ι K) *ᵥ x = x}
  one_mem' := ⟨by simpa using W.zero_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · simpa [Units.val_mul, ← Matrix.mulVec_mulVec, sub_add_sub_cancel] using
        W.add_mem (ha1 ((b : Matrix ι ι K) *ᵥ x)) (hb1 x)
    · simpa [Units.val_mul, ← Matrix.mulVec_mulVec, hb2 x hx] using ha2 x hx
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · have h := W.neg_mem (ha1 (((a⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x))
      rwa [mulVec_inv_mulVec, neg_sub] at h
    · rw [← ha2 x hx, inv_mulVec_mulVec, ha2 x hx]

theorem mem_unipotentRadical_iff {W : Submodule K (ι → K)} {g : GL ι K} :
    g ∈ unipotentRadical W ↔ (∀ x, (g : Matrix ι ι K) *ᵥ x - x ∈ W) ∧
      ∀ x ∈ W, (g : Matrix ι ι K) *ᵥ x = x :=
  Iff.rfl

theorem mul_self_eq_one_of_mem_unipotentRadical [CharP K 2]
    {W : Submodule K (ι → K)} {g : GL ι K} (hg : g ∈ unipotentRadical W) :
    g * g = 1 := by
  have hg' := mem_unipotentRadical_iff.mp hg
  have hfix : ∀ x, (g : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ x) = x := by
    intro x
    have hgy := hg'.2 _ (hg'.1 x)
    calc (g : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ x)
        = (g : Matrix ι ι K) *ᵥ (x + ((g : Matrix ι ι K) *ᵥ x - x)) := by
            rw [add_sub_cancel]
      _ = x := by
            rw [Matrix.mulVec_add, hgy]
            funext i
            simp only [Pi.add_apply, Pi.sub_apply, CharTwo.sub_eq_add, CharTwo.add_cancel_left]
  refine Units.ext (Matrix.ext_of_mulVec_single fun j => ?_)
  simpa only [Units.val_mul, ← Matrix.mulVec_mulVec, Units.val_one, Matrix.one_mulVec]
    using hfix (Pi.single j 1)

theorem isPGroup_unipotentRadical [CharP K 2] (W : Submodule K (ι → K)) :
    IsPGroup 2 (unipotentRadical W) := by
  refine fun g => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (mul_self_eq_one_of_mem_unipotentRadical g.2)⟩

theorem inv_mulVec_mem_of_forall_mulVec_mem {W : Submodule K (ι → K)} {h : GL ι K}
    (hW : ∀ x ∈ W, (h : Matrix ι ι K) *ᵥ x ∈ W) :
    ∀ x ∈ W, ((h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x ∈ W := by
  let e : (ι → K) ≃ₗ[K] (ι → K) := (Matrix.GeneralLinearGroup.toLin h).toLinearEquiv
  have he : e.toLinearMap = (h : Matrix ι ι K).mulVecLin :=
    LinearMap.ext fun x => by simp [e]
  have hmap : W.map e.toLinearMap = W :=
    Submodule.eq_of_le_of_finrank_eq
      (by rintro x ⟨y, hy, rfl⟩; rw [he, Matrix.mulVecLin_apply]; exact hW y hy)
      (by rw [LinearEquiv.finrank_map_eq])
  intro x hx
  obtain ⟨y, hyW, rfl⟩ := show x ∈ W.map e.toLinearMap by rwa [hmap]
  rw [he, Matrix.mulVecLin_apply, inv_mulVec_mulVec]
  exact hyW

theorem conj_mem_unipotentRadical {W : Submodule K (ι → K)} {h g : GL ι K}
    (hW : ∀ x ∈ W, (h : Matrix ι ι K) *ᵥ x ∈ W)
    (hg : g ∈ unipotentRadical W) : h * g * h⁻¹ ∈ unipotentRadical W := by
  have hWinv := inv_mulVec_mem_of_forall_mulVec_mem (W := W) hW
  rw [mem_unipotentRadical_iff] at hg ⊢
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · convert hW _ (hg.1 (((h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x)) using 1
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_sub, mulVec_inv_mulVec]
  · have h := congrArg (fun y => (h : Matrix ι ι K) *ᵥ y) (hg.2 _ (hWinv x hx))
    simpa only [Units.val_mul, ← Matrix.mulVec_mulVec, ← Units.val_inv_eq_inv_val,
      mulVec_inv_mulVec] using h

theorem mem_normalizer_unipotentRadical {W : Submodule K (ι → K)} {h : GL ι K}
    (hW : ∀ x ∈ W, (h : Matrix ι ι K) *ᵥ x ∈ W) :
    h ∈ Subgroup.normalizer (unipotentRadical W : Set (GL ι K)) := by
  rw [Subgroup.mem_normalizer_iff]
  refine fun g => ⟨conj_mem_unipotentRadical hW, fun hg => ?_⟩
  simpa [mul_assoc] using conj_mem_unipotentRadical (W := W) (h := h⁻¹)
    (inv_mulVec_mem_of_forall_mulVec_mem (W := W) hW) hg

end CFSG.LinearAlgebra
