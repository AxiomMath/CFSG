module

public import CFSG.GroupTheory.HuppertProduct.Mho

public section

namespace CFSG.GroupTheory.HuppertProduct

universe u

variable {G : Type u} [Group G]

theorem exists_quotient {H N : Subgroup G} (hN : H ≤ Subgroup.normalizer (N : Set G)) :
    ∃ (Γ : Type u) (_ : Group Γ) (π : H →* Γ), Function.Surjective π ∧
      ∀ a : H, π a = 1 ↔ (a : G) ∈ N := by
  haveI : (N.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  exact ⟨H ⧸ N.subgroupOf H, inferInstance, QuotientGroup.mk' (N.subgroupOf H),
    QuotientGroup.mk'_surjective _, fun a => QuotientGroup.eq_one_iff a⟩

theorem le_normalizer_sup {H A B : Subgroup G} (hA : H ≤ Subgroup.normalizer (A : Set G))
    (hB : H ≤ Subgroup.normalizer (B : Set G)) :
    H ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro h hh
  have hA' := hA hh
  have hB' := hB hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA' hB' ⊢
  rw [Subgroup.map_sup, hA', hB']

theorem le_normalizer_mho_mho (H : Subgroup G) (n m : ℕ) :
    H ≤ Subgroup.normalizer (mho (mho H n) m : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro h hh x hx
  exact conj_mem_mho (fun s hs => (Subgroup.le_normalizer_iff.1 (mho_le_normalizer H n) h hh s hs))
    hx

instance normal_subgroupOf_mho (S : Subgroup G) (n : ℕ) : ((mho S n).subgroupOf S).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (mho_le_normalizer S n)

end CFSG.GroupTheory.HuppertProduct
