module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves

open Matrix
open scoped commutatorElement Pointwise

theorem cube_eq_one_imp {F : Type} [Field F] [Finite F] (hq : Nat.card F % 3 = 2) {z : F}
    (hz : z ^ 3 = 1) : z = 1 := by
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at hq
  by_cases h0 : z = 0
  · subst h0
    simp at hz
  · have hf := FiniteField.pow_card_sub_one_eq_one z h0
    obtain ⟨a, ha⟩ : ∃ a, Fintype.card F - 1 = 3 * a + 1 := ⟨(Fintype.card F - 2) / 3, by omega⟩
    rw [ha, pow_succ, pow_mul, hz, one_pow, one_mul] at hf
    exact hf

theorem cube_bijective {F : Type} [Field F] [Finite F] (hq : Nat.card F % 3 = 2) :
    Function.Bijective (fun x : F => x ^ 3) := by
  refine Finite.injective_iff_bijective.mp ?_
  intro x y hxy
  simp only at hxy
  by_cases hy : y = 0
  · subst hy
    have hx : x ^ 3 = 0 := by simpa using hxy
    simpa using hx
  · have h1 : (x / y) ^ 3 = 1 := by
      rw [div_pow, hxy, div_self (pow_ne_zero 3 hy)]
    exact (div_eq_one_iff_eq hy).mp (cube_eq_one_imp hq h1)

theorem sq_add_self_add_one_ne_zero {F : Type} [Field F] [Finite F] (hq : Nat.card F % 3 = 2)
    (x : F) : x ^ 2 + x + 1 ≠ 0 := by
  intro h
  have := Fintype.ofFinite F
  have hq' := hq
  rw [Nat.card_eq_fintype_card] at hq'
  have hx3 : x ^ 3 = 1 := by linear_combination (x - 1) * h
  have hx1 : x = 1 := cube_eq_one_imp hq hx3
  subst hx1
  have h3 : (3 : F) = 0 := by linear_combination h
  have hc : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
  have hk : Fintype.card F = 3 * (Fintype.card F / 3) + 2 := by omega
  rw [hk] at hc
  push_cast at hc
  rw [h3, zero_mul, zero_add] at hc
  have h1 : (1 : F) = 0 := by linear_combination h3 - hc
  exact one_ne_zero h1

theorem exists_conj_eq_of_card_eq_three {G : Type} [Group G] [Finite G]
    (hcyc : ∀ X : Subgroup G, IsPGroup 3 X → IsCyclic X) {A B : Subgroup G}
    (hA : Nat.card A = 3) (hB : Nat.card B = 3) :
    ∃ g : G, B = A.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by rw [hA]; norm_num)
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by rw [hB]; norm_num)
  obtain ⟨P, hAP⟩ := hA3.exists_le_sylow
  obtain ⟨Q, hBQ⟩ := hB3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hcoe : (Q : Set G) = MulAut.conj g • (P : Set G) := by
    rw [← hg]
    exact Sylow.coe_smul
  set A' := A.map (MulAut.conj g).toMonoidHom with hA'
  have hA'Q : A' ≤ (Q : Subgroup G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxP : x ∈ (P : Set G) := hAP hx
    show MulAut.conj g x ∈ (Q : Set G)
    rw [hcoe]
    exact Set.mem_smul_set.mpr ⟨x, hxP, rfl⟩
  have hA'card : Nat.card A' = 3 := by
    rw [hA', Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g)), hA]
  have : IsCyclic (Q : Subgroup G) := hcyc _ Q.isPGroup'
  have hEq : B.subgroupOf Q = A'.subgroupOf Q := by
    rw [IsCyclic.subgroup_eq_iff_card_eq]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'Q).toEquiv, hB, hA'card]
  refine ⟨g, ?_⟩
  have h1 := Subgroup.subgroupOf_map_subtype B (Q : Subgroup G)
  have h2 := Subgroup.subgroupOf_map_subtype A' (Q : Subgroup G)
  rw [hEq, inf_eq_left.mpr hBQ] at h1
  rw [inf_eq_left.mpr hA'Q] at h2
  exact h1.symm.trans h2

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves

end
