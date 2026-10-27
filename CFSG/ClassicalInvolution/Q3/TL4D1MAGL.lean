module

import CFSG.ClassicalInvolution.Q3.TL4VecAddSelfEng
public import CFSG.ClassicalInvolution.Q3.AE.Models
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE Matrix

@[expose] def bin : Fin 8 → (Fin 3 → ZMod 2) :=
  ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]

@[expose] def binIdx (v : Fin 3 → ZMod 2) : Fin 8 :=
  if v = bin 0 then 0 else if v = bin 1 then 1 else if v = bin 2 then 2 else
    if v = bin 3 then 3 else if v = bin 4 then 4 else if v = bin 5 then 5 else
      if v = bin 6 then 6 else 7

theorem binIdx_bin : ∀ i, binIdx (bin i) = i := by decide

theorem bin_binIdx : ∀ v, bin (binIdx v) = v := by decide

theorem bin_injective : Function.Injective bin := fun i j h => by
  rw [← binIdx_bin i, h, binIdx_bin]

@[expose] def hplane (a : Fin 3 → ZMod 2) (c : ZMod 2) : Finset (Fin 8) :=
  Finset.univ.filter fun x => a ⬝ᵥ bin x = c

theorem hplane_mem : ∀ a : Fin 3 → ZMod 2, a ≠ 0 → ∀ c, hplane a c ∈ affinePlanes := by
  decide

theorem exists_hplane {s : Finset (Fin 8)} (hs : s ∈ affinePlanes) :
    ∃ a : Fin 3 → ZMod 2, a ≠ 0 ∧ ∃ c, s = hplane a c := by
  simp only [affinePlanes, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨![1, 0, 0], by decide, 0, by decide⟩
  · exact ⟨![1, 0, 0], by decide, 1, by decide⟩
  · exact ⟨![0, 1, 0], by decide, 0, by decide⟩
  · exact ⟨![0, 1, 0], by decide, 1, by decide⟩
  · exact ⟨![1, 1, 0], by decide, 0, by decide⟩
  · exact ⟨![1, 1, 0], by decide, 1, by decide⟩
  · exact ⟨![0, 0, 1], by decide, 0, by decide⟩
  · exact ⟨![0, 0, 1], by decide, 1, by decide⟩
  · exact ⟨![1, 0, 1], by decide, 0, by decide⟩
  · exact ⟨![1, 0, 1], by decide, 1, by decide⟩
  · exact ⟨![0, 1, 1], by decide, 0, by decide⟩
  · exact ⟨![0, 1, 1], by decide, 1, by decide⟩
  · exact ⟨![1, 1, 1], by decide, 0, by decide⟩
  · exact ⟨![1, 1, 1], by decide, 1, by decide⟩

theorem zmod_two_add_eq_iff : ∀ x y c : ZMod 2, x + y = c ↔ x = c + y := by decide

@[expose] def aapply (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b : Fin 3 → ZMod 2)
    (x : Fin 8) : Fin 8 :=
  binIdx (A.1 *ᵥ bin x + b)

theorem bin_aapply (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b : Fin 3 → ZMod 2)
    (x : Fin 8) : bin (aapply A b x) = A.1 *ᵥ bin x + b :=
  bin_binIdx _

theorem inv_mul_val (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : (A⁻¹).1 * A.1 = 1 :=
  congrArg Subtype.val (inv_mul_cancel A)

theorem mul_inv_val (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : A.1 * (A⁻¹).1 = 1 :=
  congrArg Subtype.val (mul_inv_cancel A)

theorem two_smul_zero (v : Fin 3 → ZMod 2) : v + v = 0 :=
  CFSG.ClassicalInvolution.Q3.TL4.vec_add_self_gen v

theorem aapply_aapply (A B : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b c : Fin 3 → ZMod 2)
    (x : Fin 8) : aapply A b (aapply B c x) = aapply (A * B) (A.1 *ᵥ c + b) x := by
  apply bin_injective
  rw [bin_aapply, bin_aapply, bin_aapply, mulVec_add, mulVec_mulVec, add_assoc]
  rfl

theorem aapply_one (x : Fin 8) : aapply 1 0 x = x := by
  apply bin_injective
  rw [bin_aapply, add_zero]
  exact one_mulVec _

theorem aapply_inv (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b : Fin 3 → ZMod 2)
    (x : Fin 8) : aapply A⁻¹ ((A⁻¹).1 *ᵥ b) (aapply A b x) = x := by
  rw [aapply_aapply, inv_mul_cancel, ← mulVec_add, two_smul_zero, mulVec_zero, aapply_one]

theorem aapply_inv' (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b : Fin 3 → ZMod 2)
    (x : Fin 8) : aapply A b (aapply A⁻¹ ((A⁻¹).1 *ᵥ b) x) = x := by
  rw [aapply_aapply, mul_inv_cancel, mulVec_mulVec, mul_inv_val, one_mulVec, two_smul_zero,
    aapply_one]

@[expose] def aperm (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b : Fin 3 → ZMod 2) :
    Equiv.Perm (Fin 8) where
  toFun := aapply A b
  invFun := aapply A⁻¹ ((A⁻¹).1 *ᵥ b)
  left_inv := aapply_inv A b
  right_inv := aapply_inv' A b

theorem aperm_apply (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b : Fin 3 → ZMod 2)
    (x : Fin 8) : aperm A b x = aapply A b x := rfl

theorem aperm_mul (A B : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b c : Fin 3 → ZMod 2) :
    aperm A b * aperm B c = aperm (A * B) (A.1 *ᵥ c + b) :=
  Equiv.ext fun x => by rw [Equiv.Perm.mul_apply, aperm_apply, aperm_apply, aperm_apply,
    aapply_aapply]

theorem aperm_inv_apply (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b : Fin 3 → ZMod 2)
    (x : Fin 8) : (aperm A b)⁻¹ x = aapply A⁻¹ ((A⁻¹).1 *ᵥ b) x := rfl

theorem aperm_inv (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b : Fin 3 → ZMod 2) :
    (aperm A b)⁻¹ = aperm A⁻¹ ((A⁻¹).1 *ᵥ b) :=
  Equiv.ext fun x => by rw [aperm_inv_apply, aperm_apply]

theorem map_hplane (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b : Fin 3 → ZMod 2)
    (a : Fin 3 → ZMod 2) (c : ZMod 2) :
    (hplane a c).map (aperm A b).toEmbedding =
      hplane (a ᵥ* (A⁻¹).1) (c + (a ᵥ* (A⁻¹).1) ⬝ᵥ b) := by
  ext z
  rw [Finset.mem_map_equiv, hplane, hplane, Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [show (aperm A b).symm z = (aperm A b)⁻¹ z from rfl, aperm_inv_apply, bin_aapply,
    dotProduct_add,
    dotProduct_mulVec, dotProduct_mulVec, zmod_two_add_eq_iff]

theorem vecMul_inv_ne_zero (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    {a : Fin 3 → ZMod 2} (ha : a ≠ 0) : a ᵥ* (A⁻¹).1 ≠ 0 := by
  intro h
  apply ha
  have : a ᵥ* (A⁻¹).1 ᵥ* A.1 = a := by rw [vecMul_vecMul, inv_mul_val, vecMul_one]
  rw [← this, h, zero_vecMul]

theorem aperm_mem_agl32 (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b : Fin 3 → ZMod 2) :
    aperm A b ∈ agl32 := by
  have key : ∀ (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b : Fin 3 → ZMod 2),
      ∀ s ∈ affinePlanes, s.map (aperm A b).toEmbedding ∈ affinePlanes := by
    intro A b s hs
    obtain ⟨a, ha, c, rfl⟩ := exists_hplane hs
    rw [map_hplane]
    exact hplane_mem _ (vecMul_inv_ne_zero A ha) _
  intro s hs
  exact ⟨key A b s hs, by rw [aperm_inv]; exact key _ _ s hs⟩

end CFSG.ClassicalInvolution.Q3.TL4
