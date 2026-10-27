module

public import CFSG.LocalAnalysis.ComponentInitial.BlockSylowOrder

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification OuterAutomorphisms

variable {G : Type*} [Group G]

@[expose] noncomputable def quotientActionHom (X : Subgroup G) {N : Subgroup G}
    (hN : N ≤ normalizer (X : Set G)) : N →* MulAut (X ⧸ center X) :=
  (PerfectAutomorphisms.centerQuotientHom X).comp
    ((normalizerConjHom X).comp (Subgroup.inclusion hN))

theorem ker_quotientActionHom {X N : Subgroup G} [Group.IsPerfect X]
    (hN : N ≤ normalizer (X : Set G)) :
    (quotientActionHom X hN).ker = (centralizer (X : Set G)).subgroupOf N := by
  ext n
  rw [MonoidHom.mem_ker, quotientActionHom, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
  have h := congrArg (fun S : Subgroup _ => Subgroup.inclusion hN n ∈ S)
    (ker_centerQuotient_comp_normalizerConjHom X)
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
    Subgroup.coe_inclusion, eq_iff_iff] at h
  exact h

theorem inner_le_range_quotientActionHom {X N : Subgroup G} (hN : N ≤ normalizer (X : Set G))
    (hXN : X ≤ N) : OuterAutomorphisms.inner (X ⧸ center X) ≤ (quotientActionHom X hN).range := by
  rintro _ ⟨τ, rfl⟩
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (center X) τ
  refine ⟨⟨j, hXN j.2⟩, ?_⟩
  rw [quotientActionHom, MonoidHom.comp_apply, ← centerQuotient_conj]
  congr 1

variable [Finite G]

omit [Finite G] in
theorem quotientActionHom_eq_one_of_mem_centralizer {K N : Subgroup G}
    (hN : N ≤ normalizer (K : Set G)) {n : N} (hn : (n : G) ∈ centralizer (K : Set G)) :
    quotientActionHom K hN n = 1 := by
  have h : normalizerConjHom K (Subgroup.inclusion hN n) = 1 := by
    have := (ker_normalizerConjHom K).symm ▸ (Subgroup.mem_subgroupOf.2 hn :
      Subgroup.inclusion hN n ∈ (centralizer (K : Set G)).subgroupOf (normalizer (K : Set G)))
    exact MonoidHom.mem_ker.1 this
  rw [quotientActionHom, MonoidHom.comp_apply, MonoidHom.comp_apply, h, map_one]

omit [Finite G] in
theorem quotientActionHom_mem_eq_conj {X N : Subgroup G} (hN : N ≤ normalizer (X : Set G))
    (hXN : X ≤ N) (j : X) :
    quotientActionHom X hN ⟨j, hXN j.2⟩ = MulAut.conj (QuotientGroup.mk' (center X) j) := by
  rw [quotientActionHom, MonoidHom.comp_apply, ← centerQuotient_conj]
  congr 1

end CFSG.LocalAnalysis.ComponentInitial
