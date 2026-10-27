module


public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.IndependentSummandFixedVectorSupportStable

theorem stable_support {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    {H : Type*} [Group H] {I : Type*} [Fintype I] [MulAction H I]
    (U : I → Submodule F V) (hU : iSupIndep U)
    (ρ : Representation F H V) (hperm : ∀ (h : H) (i : I), (U i).map (ρ h) = U (h • i))
    (B : Subgroup H) (w : I → V) (hw : ∀ i, w i ∈ U i) (v : V) (hsum : ∑ i, w i = v)
    (hfix : ∀ b : B, ρ b.val v = v) (b : B) (i : I) :
    w i ≠ 0 ↔ w (b.val • i) ≠ 0 := by
  classical
  have hmem : ∀ (h : H) (i : I), ρ h (w i) ∈ U (h • i) := fun h i => by
    rw [← hperm h i]; exact Submodule.mem_map_of_mem (hw i)
  have hsumeq : ∑ j, ρ b.val (w (b.val⁻¹ • j)) = ∑ j, w j := by
    have h1 : ρ b.val (∑ j, w j) = ∑ j, w j := by rw [hsum]; exact hfix b
    rw [← h1, map_sum]
    rw [← Equiv.sum_comp (MulAction.toPerm b.val) (fun j => ρ b.val (w (b.val⁻¹ • j)))]
    simp
  have key := (iSupIndep_iff_finsetSum_eq_imp_eq U).1 hU Finset.univ
    (fun j => ρ b.val (w (b.val⁻¹ • j))) w
    (fun j _ => ⟨by simpa using hmem b.val (b.val⁻¹ • j), hw j⟩) hsumeq (b.val • i)
    (Finset.mem_univ _)
  simp only [inv_smul_smul] at key
  have hinj : Function.Injective (ρ b.val) := by
    intro x y hxy
    have := congrArg (ρ b.val⁻¹) hxy
    simpa [← Module.End.mul_apply, ← map_mul] using this
  rw [← key]
  constructor
  · intro h h0
    exact h (hinj (by simpa using h0))
  · intro h h0
    exact h (by simp [h0])

theorem support_nonempty {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    {I : Type*} [Fintype I] (w : I → V) (v : V) (hsum : ∑ i, w i = v) (hv : v ≠ 0) :
    ∃ i, w i ≠ 0 := by
  by_contra h
  push Not at h
  exact hv (by simp [← hsum, h])

end CFSG.GroupTheory.CoprimeActionSupport.IndependentSummandFixedVectorSupportStable
