module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Tr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G}

theorem sec5p510c_t_mul_t (h : Sec510Ctx G t L S z r ρ B A φ) : t * t = 1 := by
  have h2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [h.involution] at this
  rwa [pow_two] at h2

theorem sec5p510c_W1_subset_delta (h : Sec510Ctx G t L S z r ρ B A φ) :
    wclass φ 1 ⊆ conjClassIn (normalizer (A : Set G)) t := by
  rw [h.delta]
  exact Set.subset_union_right

theorem sec5p510c_t_mul_mem (h : Sec510Ctx G t L S z r ρ B A φ) {k : ℕ} (hk : k ≤ 6) {x : G}
    (hx : x ∈ wclass φ k) : t * x ∈ wclass φ (6 - k) := by
  have h1 := h.model.perm.mul_mem_wclass hk hx
  have ht : φ (1 : Fin 6 → ZMod 2) = t := by
    rw [Pi.one_def]
    exact h.model.map_one
  rwa [ht] at h1

theorem sec5p510c_exists_third (h : Sec510Ctx G t L S z r ρ B A φ) {x y : G} :
    ∃ w ∈ conjClassIn (normalizer (A : Set G)) t, w ≠ x ∧ w ≠ y := by
  by_contra hcon
  have hsub : wclass φ 1 ⊆ ({x, y} : Set G) := by
    intro w hw
    by_cases hwx : w = x
    · exact Or.inl hwx
    · by_contra hwy
      exact hcon ⟨w, sec5p510c_W1_subset_delta h hw, hwx, fun e => hwy (Or.inr e)⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({x, y} : Set G).ncard ≤ 2 :=
    (Set.ncard_insert_le x {y}).trans (by simp)
  rw [h.model.perm.ncard_wclass 1] at h1
  have h3 : Nat.choose 6 1 = 6 := by decide
  omega

theorem sec5p510c_two_trans (h : Sec510Ctx G t L S z r ρ B A φ) {x y x' y' : G}
    (hx : x ∈ conjClassIn (normalizer (A : Set G)) t)
    (hy : y ∈ conjClassIn (normalizer (A : Set G)) t)
    (hx' : x' ∈ conjClassIn (normalizer (A : Set G)) t)
    (hy' : y' ∈ conjClassIn (normalizer (A : Set G)) t) (hxy : x ≠ y) (hxy' : x' ≠ y') :
    ∃ m ∈ normalizer (A : Set G), m * x * m⁻¹ = x' ∧ m * y * m⁻¹ = y' := by
  obtain ⟨w, hw, hwx, hwy⟩ := sec5p510c_exists_third h (x := x) (y := y)
  obtain ⟨w', hw', hwx', hwy'⟩ := sec5p510c_exists_third h (x := x') (y := y')
  obtain ⟨m, hm, h1, h2, -⟩ := sec5p510_triple h hx hy hw hx' hy' hw' hxy (Ne.symm hwx)
    (Ne.symm hwy) hxy' (Ne.symm hwx') (Ne.symm hwy')
  exact ⟨m, hm, h1, h2⟩

end CFSG.OddStandard.SmallF3.Omega
