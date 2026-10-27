module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Semidihedral.Principal.ColumnAverageBound

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Principal

namespace LocalParameterFiveCentralSplitting

theorem sup_zpowers_eq_top_of_index_eq_two {G : Type*} [Group G] {Y : Subgroup G}
    (hY : Y.index = 2) {x : G} (hx : x ∉ Y) : Y ⊔ Subgroup.zpowers x = ⊤ := by
  set M := Y ⊔ Subgroup.zpowers x with hM
  have hYM : Y ≤ M := le_sup_left
  have h := Subgroup.relIndex_mul_index hYM
  rw [hY] at h
  have hne : Y.relIndex M ≠ 1 := by
    intro h1
    exact hx (Subgroup.relIndex_eq_one.mp h1 (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  have hM1 : M.index = 1 := by
    have hdvd : Y.relIndex M ∣ 2 := ⟨M.index, h.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd h1 hne
    · rw [h2] at h
      omega
  exact Subgroup.index_eq_one.mp hM1

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {s z : G} (hs : s ^ 2 = 1)
    (hz : z ∈ Subgroup.zpowers s) : z = 1 ∨ z = s := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hs2 : s ^ (2 : ℤ) = 1 := by exact_mod_cast hs
  have hk : s ^ k = s ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, hs2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [hk, h0, zpow_zero]
  · right
    rw [hk, h1, zpow_one]

theorem semidirectProduct_inl_bijective {N K : Type*} [Group N] [Group K] [Subsingleton K]
    (φ : K →* MulAut N) : Function.Bijective (SemidirectProduct.inl : N →* N ⋊[φ] K) := by
  refine ⟨SemidirectProduct.inl_injective, fun g => ⟨g.left, ?_⟩⟩
  apply SemidirectProduct.ext
  · rfl
  · exact Subsingleton.elim _ _

end LocalParameterFiveCentralSplitting

end CFSG.Semidihedral.Principal
