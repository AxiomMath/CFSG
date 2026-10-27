module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.SylowTransport
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux

public section

namespace CFSG.AGLEmbedding.Norton.OrdinaryProofs

open CFSG.Open

theorem glbCore_two_top_of_normalizing {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {ι : Type*} (P : Subgroup G) (hP : IsPGroup p P) (Q : ι → Subgroup G)
    (hQP : ∀ i, Q i ≤ P) (h2 : ∀ i, 2 ≤ pRank p (Q i)) (S : Set G)
    (hS : Subgroup.closure S = ⊤) (hSN : ∀ s ∈ S, ∃ i, s ∈ Subgroup.normalizer (Q i : Set G)) :
    ∀ T : Sylow p G, GLBCore p 2 (T : Subgroup G) = ⊤ := by
  obtain ⟨T₀, hT₀⟩ := hP.exists_le_sylow
  have hcore : GLBCore p 2 (T₀ : Subgroup G) = ⊤ := by
    have hS' : S ⊆ (GLBCore p 2 (T₀ : Subgroup G) : Set G) := by
      intro s hs
      obtain ⟨i, hi⟩ := hSN s hs
      have hmem : Subgroup.normalizer (Q i : Set G) ≤ GLBCore p 2 (T₀ : Subgroup G) := by
        unfold GLBCore
        exact le_sSup ⟨Q i, (hQP i).trans hT₀, h2 i, rfl⟩
      exact hmem hi
    have hcl : Subgroup.closure S ≤ GLBCore p 2 (T₀ : Subgroup G) :=
      (Subgroup.closure_le _).mpr hS'
    rw [hS] at hcl
    exact top_le_iff.mp hcl
  intro T
  exact GLBCore_top_of_one_sylow T₀ hcore T

theorem two_le_pRank_of_commute {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} {x y : G} (hxH : x ∈ H) (hyH : y ∈ H) (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : Commute x y) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) :
    2 ≤ pRank p H :=
  CFSG.AGLEmbedding.two_le_pRank_of_commute_of_not_mem_zpowers Fact.out
    (orderOf_eq_prime hx hx1) hy hyx hxy hxH hyH

end CFSG.AGLEmbedding.Norton.OrdinaryProofs

end
