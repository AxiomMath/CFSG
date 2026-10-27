module

public import CFSG.CharacterTheory.Wreathed.BaseAndDerived

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem element_base_zpow (m : ℕ) (a b : ZMod m) (k : ℤ) :
    element m a b 0 ^ k = element m (k • a) (k • b) 0 := by
  cases k with
  | ofNat k =>
    change element m a b 0 ^ (k : ℤ) = element m ((k : ℤ) • a) ((k : ℤ) • b) 0
    simpa only [zpow_natCast, natCast_zsmul] using element_base_pow m a b k
  | negSucc k =>
    rw [zpow_negSucc, element_base_pow, element_base_inv]
    simp only [Int.negSucc_eq, neg_smul, add_smul, natCast_zsmul, one_smul]

theorem element_first_mem_zpowers (m : ℕ) (a : ZMod m) :
    element m a 0 0 ∈ Subgroup.zpowers (element m 1 0 0) := by
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective a
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨k, ?_⟩
  rw [element_base_zpow]
  simpa only [zsmul_eq_mul, mul_one, mul_zero] using
    congrArg (fun c : ZMod m => element m c 0 0) hk

theorem element_second_mem_zpowers (m : ℕ) (b : ZMod m) :
    element m 0 b 0 ∈ Subgroup.zpowers (element m 0 1 0) := by
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective b
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨k, ?_⟩
  rw [element_base_zpow]
  simpa only [zsmul_eq_mul, mul_one, mul_zero] using
    congrArg (fun c : ZMod m => element m 0 c 0) hk

theorem base_eq_generated (m : ℕ) :
    baseSubgroup m = Subgroup.closure {element m 1 0 0, element m 0 1 0} := by
  let H := Subgroup.closure {element m 1 0 0, element m 0 1 0}
  have hs : element m 1 0 0 ∈ H := Subgroup.subset_closure (by simp)
  have ht : element m 0 1 0 ∈ H := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
    change element m a b e ∈ baseSubgroup m at hg
    change element m a b e ∈ H
    rw [(element_mem_base m a b e).mp hg]
    have ha : element m a 0 0 ∈ H :=
      Subgroup.zpowers_le_of_mem hs (element_first_mem_zpowers m a)
    have hb : element m 0 b 0 ∈ H :=
      Subgroup.zpowers_le_of_mem ht (element_second_mem_zpowers m b)
    simpa only [element_base_mul, add_zero, zero_add] using H.mul_mem ha hb
  · rw [Subgroup.closure_le]
    intro g hg
    rcases Set.mem_insert_iff.mp hg with hg | hg
    · rw [hg]
      simp
    · rw [Set.mem_singleton_iff.mp hg]
      simp

theorem wreath_eq_generated_s_swap (m : ℕ) :
    Subgroup.closure {element m 1 0 0, element m 0 0 1} = ⊤ := by
  let H := Subgroup.closure {element m 1 0 0, element m 0 0 1}
  have hs : element m 1 0 0 ∈ H := Subgroup.subset_closure (by simp)
  have hz : element m 0 0 1 ∈ H := Subgroup.subset_closure (by simp)
  have ht : element m 0 1 0 ∈ H := by
    have hp := H.mul_mem (H.mul_mem hz hs) (H.inv_mem hz)
    rw [conjugate_base_by_swap] at hp
    exact hp
  have hbase : baseSubgroup m ≤ H := by
    rw [base_eq_generated, Subgroup.closure_le]
    intro g hg
    rcases Set.mem_insert_iff.mp hg with hg | hg
    · exact hg ▸ hs
    · exact Set.mem_singleton_iff.mp hg ▸ ht
  apply top_unique
  intro g _
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
  change element m a b e ∈ H
  have hb : element m a b 0 ∈ H := hbase (by simp)
  rcases swap_exponent_cases e with rfl | rfl
  · exact hb
  · simpa only [element_base_mul, add_zero] using H.mul_mem hb hz

theorem wreathHom_ext {M : Type*} [Monoid M] (m : ℕ) {f g : Wreath m →* M}
    (hs : f (element m 1 0 0) = g (element m 1 0 0))
    (hz : f (element m 0 0 1) = g (element m 0 0 1)) : f = g := by
  apply MonoidHom.eq_of_eqOn_dense (wreath_eq_generated_s_swap m)
  intro a ha
  rcases Set.mem_insert_iff.mp ha with ha | ha
  · exact ha ▸ hs
  · exact Set.mem_singleton_iff.mp ha ▸ hz

theorem wreathHom_ext_iff {M : Type*} [Monoid M] (m : ℕ) (f g : Wreath m →* M) :
    f = g ↔ f (element m 1 0 0) = g (element m 1 0 0) ∧
      f (element m 0 0 1) = g (element m 0 0 1) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hs, hz⟩
    exact wreathHom_ext m hs hz

end CFSG.Wreathed
