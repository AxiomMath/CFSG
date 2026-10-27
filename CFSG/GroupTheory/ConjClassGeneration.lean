module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

theorem eq_top_of_mem_of_closure_isConj_eq_top {G : Type*} [Group G] {S : Subgroup G}
    (hS : S.Normal) {x : G} (hx : x ∈ S)
    (hgen : Subgroup.closure {y | IsConj x y} = ⊤) : S = ⊤ := by
  have hsub : {y : G | IsConj x y} ⊆ S := by
    rintro y hy
    obtain ⟨c, hc⟩ := isConj_iff.1 hy
    rw [← hc]
    exact hS.conj_mem x hx c
  have hle : Subgroup.closure {y : G | IsConj x y} ≤ S := (Subgroup.closure_le S).2 hsub
  rw [hgen] at hle
  exact top_le_iff.1 hle

theorem closure_isConj_mulEquiv_eq_top {G H : Type*} [Group G] [Group H] (e : G ≃* H) {x : G}
    (hgen : Subgroup.closure {y | IsConj x y} = ⊤) :
    Subgroup.closure {y : H | IsConj (e x) y} = ⊤ := by
  have h1 : Subgroup.closure (e '' {y : G | IsConj x y}) = ⊤ := by
    have h := MonoidHom.map_closure (e : G →* H) {y : G | IsConj x y}
    rw [hgen, Subgroup.map_equiv_top] at h
    rw [h]
    rfl
  have hle : Subgroup.closure (e '' {y : G | IsConj x y}) ≤
      Subgroup.closure {y : H | IsConj (e x) y} :=
    Subgroup.closure_mono (by
      rintro y ⟨z, hz, rfl⟩
      exact MonoidHom.map_isConj (e : G →* H) hz)
  rw [h1] at hle
  exact top_le_iff.1 hle

theorem conj_mem_closure_iUnion_conj {G : Type*} [Group G] (N : Subgroup G) (T : Set G)
    {n : G} (hn : n ∈ N) {c : G}
    (hc : c ∈ Subgroup.closure (⋃ m ∈ N, (fun s => m * s * m⁻¹) '' T)) :
    n * c * n⁻¹ ∈ Subgroup.closure (⋃ m ∈ N, (fun s => m * s * m⁻¹) '' T) := by
  refine Subgroup.closure_induction
    (p := fun c _ => n * c * n⁻¹ ∈ Subgroup.closure (⋃ m ∈ N, (fun s => m * s * m⁻¹) '' T))
    ?_ ?_ ?_ ?_ hc
  · intro u hu
    simp only [Set.mem_iUnion, Set.mem_image] at hu
    obtain ⟨m, hm, j, hj, rfl⟩ := hu
    apply Subgroup.subset_closure
    simp only [Set.mem_iUnion, Set.mem_image]
    exact ⟨n * m, N.mul_mem hn hm, j, hj, by group⟩
  · simp
  · intro u v _ _ ihu ihv
    simpa [mul_assoc] using Subgroup.mul_mem _ ihu ihv
  · intro u _ ihu
    simpa [mul_assoc] using Subgroup.inv_mem _ ihu

end CFSG.GroupTheory
