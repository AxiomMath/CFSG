module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LeviModules

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open scoped Matrix

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

@[expose] def slThree : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀ :=
  ⟨!![0, 1; 1, 1], by simp [Matrix.det_fin_two, d.neg_one_Γ₀]⟩

theorem slThree_pow_three : d.slThree ^ 3 = 1 := by
  have h2 : (1 : d.Γ₀) + 1 = 0 := d.add_self_Γ₀ 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  show !![(0 : d.Γ₀), 1; 1, 1] ^ 3 = 1
  rw [pow_succ, pow_succ, pow_one, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [h2]

theorem slThree_ne_one : d.slThree ≠ 1 := fun h => by
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀ =>
    (A : Matrix (Fin 2) (Fin 2) d.Γ₀) 0 0) h
  simp [slThree] at this

@[expose] noncomputable def leviThree : X :=
  ((d.leviLongEquiv.symm d.slThree : d.leviLong) : X)

theorem leviThree_mem_leviLong : d.leviThree ∈ d.leviLong :=
  (d.leviLongEquiv.symm d.slThree).2

theorem leviThree_pow_three : d.leviThree ^ 3 = 1 := by
  have h : (d.leviLongEquiv.symm d.slThree) ^ 3 = 1 := by
    rw [← map_pow, d.slThree_pow_three, map_one]
  have := congrArg Subtype.val h
  rwa [Subgroup.coe_pow, OneMemClass.coe_one] at this

theorem leviThree_ne_one : d.leviThree ≠ 1 := fun h => by
  apply d.slThree_ne_one
  have h' : d.leviLongEquiv.symm d.slThree = 1 := Subtype.ext h
  rw [← d.leviLongEquiv.apply_symm_apply d.slThree, h', map_one]

theorem leviThree_conj_yv (w : Fin 2 → d.Γ₀) :
    d.leviThree * d.yv w * d.leviThree⁻¹ =
      d.yv ((d.slThree : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w) := by
  have := d.leviLongRep_spec (d.leviLongEquiv.symm d.slThree) w
  rw [← d.leviLongEquiv_apply, d.leviLongEquiv.apply_symm_apply] at this
  exact this

theorem eq_zero_of_slThree_mulVec_eq {K : Type*} [Field K] {w : Fin 2 → K}
    (hw : !![(0 : K), 1; 1, 1] *ᵥ w = w) : w = 0 := by
  have e0 := congrFun hw 0
  have e1 := congrFun hw 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  funext i
  fin_cases i
  · simpa using e1
  · simpa [e1] using e0

theorem eq_one_of_mem_Y_of_leviThree_conj {y : X} (hy : y ∈ d.Y)
    (h : d.leviThree * y * d.leviThree⁻¹ = y) : y = 1 := by
  have hy' : y ∈ Set.range d.yv := by rw [d.range_yv]; exact hy
  obtain ⟨w, rfl⟩ := hy'
  rw [d.leviThree_conj_yv] at h
  have hw := eq_zero_of_slThree_mulVec_eq (d.yv_injective h)
  rw [hw]
  simp [yv, d.x₅_zero, d.x₆_zero]

theorem leviLong_le_normalizer_W : d.leviLong ≤ normalizer (d.W : Set X) := by
  refine (closure_le _).2 fun g hg => ?_
  rcases hg with hg | hg
  · exact d.S_le_normalizer_W (d.U₂_le_S hg)
  · rw [Set.mem_singleton_iff.1 hg]
    exact d.v_mem_normalizer_W_of_Y

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
