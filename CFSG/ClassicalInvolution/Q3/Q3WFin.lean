module

public import CFSG.ClassicalInvolution.WeakCT.Defs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

abbrev F3 : Type := ZMod 3

@[expose] def xp {K : Type} [Field K] (t : K) : SL(2, K) :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def xm {K : Type} [Field K] (t : K) : SL(2, K) :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def rotJ : SL(2, F3) :=
  ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two_of]; decide⟩

abbrev b0 (A : SL(2, F3)) : SL(3, F3) := blockSL F3 3 2 0 (by omega) A

abbrev b1 (B : SL(2, F3)) : SL(3, F3) := blockSL F3 3 2 1 (by omega) B

theorem xm_cases : ∀ s : F3, xm s = 1 ∨ xm s = xm 1 ∨ xm s = (xm 1)⁻¹ := by decide +kernel

theorem xp_cases : ∀ s : F3, xp s = 1 ∨ xp s = xp 1 ∨ xp s = (xp 1)⁻¹ := by decide +kernel

theorem xm_one_ne_one : (xm 1 : SL(2, F3)) ≠ 1 := by decide +kernel

theorem xp_one_ne_one : (xp 1 : SL(2, F3)) ≠ 1 := by decide +kernel

theorem xm_one_pow_three : (xm 1 : SL(2, F3)) ^ 3 = 1 := by decide +kernel

theorem xp_one_pow_three : (xp 1 : SL(2, F3)) ^ 3 = 1 := by decide +kernel

theorem xp_one_inv : (xp 1 : SL(2, F3))⁻¹ = xp (-1) := by decide +kernel

theorem xm_one_inv : (xm 1 : SL(2, F3))⁻¹ = xm (-1) := by decide +kernel

theorem unip_upper : ∀ A : SL(2, F3), A ^ 3 = 1 → A ≠ 1 → A 0 1 = 0 → ∃ s : F3, A = xm s := by
  decide +kernel

theorem unip_lower : ∀ A : SL(2, F3), A ^ 3 = 1 → A ≠ 1 → A 1 0 = 0 → ∃ s : F3, A = xp s := by
  decide +kernel

theorem comm_b0_xp_iff : ∀ t : F3, t ≠ 0 → ∀ B : SL(2, F3),
    (b0 (xp t) * b1 B = b1 B * b0 (xp t)) ↔ ∃ s : F3, B = xm s := by
  decide +kernel

theorem comm_b0_xm_iff : ∀ t : F3, t ≠ 0 → ∀ B : SL(2, F3),
    (b0 (xm t) * b1 B = b1 B * b0 (xm t)) ↔ ∃ s : F3, B = xp s := by
  decide +kernel

theorem b0_xp_one_eq : ∀ A : SL(2, F3), A 0 1 ≠ 0 →
    b0 (xp 1) = b1 rotJ * (((b0 A) * b1 (xp 1) * (b0 A)⁻¹ * (b1 (xp 1))⁻¹ *
      b1 (xp (1 - A 1 1))) ^ ((A 0 1).val)) * (b1 rotJ)⁻¹ := by
  decide +kernel

theorem b0_xm_one_eq : ∀ A : SL(2, F3), A 1 0 ≠ 0 →
    b0 (xm 1) = b1 rotJ * (((b0 A) * b1 (xm 1) * (b0 A)⁻¹ * (b1 (xm 1))⁻¹ *
      b1 (xm (1 - A 0 0))) ^ ((-A 1 0).val)) * (b1 rotJ)⁻¹ := by
  decide +kernel

theorem b0_xp_one_mem {H : Subgroup SL(3, F3)} (hB : ∀ B : SL(2, F3), b1 B ∈ H)
    {A : SL(2, F3)} (hA : A 0 1 ≠ 0) (hs : b0 A ∈ H) : b0 (xp 1) ∈ H := by
  rw [b0_xp_one_eq A hA]
  refine H.mul_mem (H.mul_mem (hB _) (H.pow_mem ?_ _)) (H.inv_mem (hB _))
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hs (hB _)) (H.inv_mem hs))
    (H.inv_mem (hB _))) (hB _)

theorem b0_xm_one_mem {H : Subgroup SL(3, F3)} (hB : ∀ B : SL(2, F3), b1 B ∈ H)
    {A : SL(2, F3)} (hA : A 1 0 ≠ 0) (hs : b0 A ∈ H) : b0 (xm 1) ∈ H := by
  rw [b0_xm_one_eq A hA]
  refine H.mul_mem (H.mul_mem (hB _) (H.pow_mem ?_ _)) (H.inv_mem (hB _))
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hs (hB _)) (H.inv_mem hs))
    (H.inv_mem (hB _))) (hB _)

theorem center_eq_bot : Subgroup.center SL(3, F3) = ⊥ := by
  have key : ∀ r : F3, r ^ Fintype.card (Fin 3) = 1 → r = 1 := by decide
  ext g
  rw [Subgroup.mem_bot, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hg⟩
    have h1 := key r hr
    subst h1
    refine Subtype.ext ?_
    rw [← hg]
    simp
  · rintro rfl
    exact ⟨1, by simp, by simp⟩

end CFSG.ClassicalInvolution.Q3.Q3W
