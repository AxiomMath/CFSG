module


public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.LinearAlgebra.CoprimeActions.DistinctCharacterEigenvectorIndependent

theorem linearIndependent {F V E I : Type*} [Field F] [AddCommGroup V] [Module F V] [Group E]
    (τ : Representation F E V) (χ : I → (E →* Fˣ)) (v : I → V) (hv : ∀ i, v i ≠ 0)
    (hEigen : ∀ i g, τ g (v i) = (χ i g : F) • v i) (hχ : Function.Injective χ) :
    LinearIndependent F v := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro c _ i hi; simp at hi
  | insert a s ha ih =>
    intro c hc i hi
    rw [Finset.sum_insert ha] at hc
    have hs : ∀ j ∈ s, c j = 0 := by
      intro j hj
      have hja : j ≠ a := fun h => ha (h ▸ hj)
      obtain ⟨g, hg⟩ : ∃ g, χ j g ≠ χ a g := by
        by_contra hcon
        push Not at hcon
        exact hja (hχ (MonoidHom.ext hcon))
      have h1 := congrArg (fun x => τ g x - (χ a g : F) • x) hc
      simp only [map_add, map_sum, map_smul, hEigen, smul_zero, map_zero, sub_zero,
        Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib] at h1
      have h2 : ∑ k ∈ s, (c k * ((χ k g : F) - (χ a g : F))) • v k = 0 := by
        rw [← h1]
        simp only [mul_sub, sub_smul]
        simp [Finset.sum_sub_distrib, smul_smul, mul_comm, mul_left_comm]
        rw [Finset.smul_sum]; simp [smul_smul, mul_comm]
      have := ih _ h2 j hj
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd (Units.ext (sub_eq_zero.1 h)) hg
    have hca : c a = 0 := by
      rw [Finset.sum_eq_zero (fun j hj => by simp [hs j hj]), add_zero] at hc
      exact (smul_eq_zero.1 hc).resolve_right (hv a)
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hca
    · exact hs i hi

end CFSG.LinearAlgebra.CoprimeActions.DistinctCharacterEigenvectorIndependent
