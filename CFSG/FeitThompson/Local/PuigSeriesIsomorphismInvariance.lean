module

public import CFSG.FeitThompson.Definitions.PuigSubgroupIteration

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {X : Type*} [Group X] {Y : Type*} [Group Y]

private theorem map_centralizer_coe_of_equiv (f : X ≃* Y) (K : Subgroup X) :
    (centralizer (K : Set X)).map f.toMonoidHom
      = centralizer ((K.map f.toMonoidHom : Subgroup Y) : Set Y) := by
  have himg : (f : X → Y) '' (K : Set X) = ((K.map f.toMonoidHom : Subgroup Y) : Set Y) := by
    simp [Subgroup.coe_map]
  refine le_antisymm ?_ ?_
  · rw [← himg]
    exact map_centralizer_le_centralizer_image _ _
  · intro y hy
    refine ⟨f.symm y, ?_, by simp⟩
    simp only [SetLike.mem_coe, mem_centralizer_iff]
    intro x hx
    have hx' : f x ∈ ((K.map f.toMonoidHom : Subgroup Y) : Set Y) := by
      rw [← himg]; exact ⟨x, hx, rfl⟩
    have h := congrArg f.symm ((mem_centralizer_iff.1 hy) (f x) hx')
    simpa using h

theorem puigSeries_map (f : X ≃* Y) (n : ℕ) :
    (puigSeries X n).map f.toMonoidHom = puigSeries Y n := by
  induction n with
  | zero => simp
  | succ n ih => rw [puigSeries_succ, puigLambda_map, ih, puigSeries_succ]

theorem image_coe_puigSeries (f : X ≃* Y) (n : ℕ) :
    (f : X → Y) '' (puigSeries X n : Set X) = (puigSeries Y n : Set Y) := by
  rw [← puigSeries_map f n]; simp [Subgroup.coe_map]

@[simp] theorem mem_puigSeries_map_iff (f : X ≃* Y) (n : ℕ) (x : X) :
    f x ∈ puigSeries Y n ↔ x ∈ puigSeries X n := by
  rw [← puigSeries_map f n]
  simp [Subgroup.mem_map_equiv]

theorem puigLower_map (f : X ≃* Y) : (puigLower X).map f.toMonoidHom = puigLower Y := by
  rw [puigLower_eq_iSup, Subgroup.map_iSup, puigLower_eq_iSup]
  exact iSup_congr fun n => puigSeries_map f (2 * n)

theorem puigUpper_map (f : X ≃* Y) : (puigUpper X).map f.toMonoidHom = puigUpper Y := by
  rw [puigUpper_eq_iInf, Subgroup.map_iInf _ f.injective, puigUpper_eq_iInf]
  exact iInf_congr fun n => puigSeries_map f (2 * n + 1)

theorem puigSubgroup_map (f : X ≃* Y) : (puigSubgroup X).map f.toMonoidHom = puigSubgroup Y := by
  rw [puigSubgroup_eq_puigUpper, puigSubgroup_eq_puigUpper, puigUpper_map]

theorem image_coe_puigSubgroup (f : X ≃* Y) :
    (f : X → Y) '' (puigSubgroup X : Set X) = (puigSubgroup Y : Set Y) := by
  rw [← puigSubgroup_map f]; simp [Subgroup.coe_map]

@[simp] theorem mem_puigSubgroup_map_iff (f : X ≃* Y) (x : X) :
    f x ∈ puigSubgroup Y ↔ x ∈ puigSubgroup X := by
  rw [← puigSubgroup_map f]
  simp [Subgroup.mem_map_equiv]

theorem puigCenter_map (f : X ≃* Y) : (puigCenter X).map f.toMonoidHom = puigCenter Y := by
  rw [puigCenter_eq_inf_centralizer, Subgroup.map_inf_eq _ _ _ f.injective,
    map_centralizer_coe_of_equiv, puigSubgroup_map, puigCenter_eq_inf_centralizer]

theorem image_coe_puigCenter (f : X ≃* Y) :
    (f : X → Y) '' (puigCenter X : Set X) = (puigCenter Y : Set Y) := by
  rw [← puigCenter_map f]; simp [Subgroup.coe_map]

@[simp] theorem mem_puigCenter_map_iff (f : X ≃* Y) (x : X) :
    f x ∈ puigCenter Y ↔ x ∈ puigCenter X := by
  rw [← puigCenter_map f]
  simp [Subgroup.mem_map_equiv]

theorem puig_map_of_equiv_finite (X : Type*) [Group X] [Finite X] (Y : Type*) [Group Y] [Finite Y]
    (f : X ≃* Y) :
    (∀ n : ℕ, (puigSeries X n).map f.toMonoidHom = puigSeries Y n) ∧
      (puigLower X).map f.toMonoidHom = puigLower Y ∧
      (puigSubgroup X).map f.toMonoidHom = puigSubgroup Y ∧
      (puigCenter X).map f.toMonoidHom = puigCenter Y :=
  ⟨puigSeries_map f, puigLower_map f, puigSubgroup_map f, puigCenter_map f⟩

end CFSG.FeitThompson

end
