module

public import CFSG.Quasithin.EmptyFaithful.SBc13JRaOdd

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5

theorem mem_normalizer_of_odd_orderOf_of_ncard_conjugates_le_two {G : Type*} [Group G] [Finite G]
    {L : Subgroup G}
    (h : {L' : Subgroup G | ∃ g : G, L' = L.map (MulAut.conj g).toMonoidHom}.ncard ≤ 2)
    {y : G} (hy : Odd (orderOf y)) : y ∈ Subgroup.normalizer (L : Set G) := by
  by_cases hall : ∀ t : G, t ∈ Subgroup.normalizer (L : Set G)
  · exact hall y
  · push_neg at hall
    obtain ⟨t, ht⟩ := hall
    refine CFSG.Quasithin.SBc13.mem_normalizer_of_odd_of_two_conjugates ht ?_ hy
    set S : Set (Subgroup G) := {L' | ∃ g : G, L' = L.map (MulAut.conj g).toMonoidHom} with hS
    have hL : L ∈ S := ⟨1, (CFSG.Quasithin.conjSub_one L).symm⟩
    have hLt : CFSG.Quasithin.conjSub t L ∈ S := ⟨t, rfl⟩
    have hne : CFSG.Quasithin.conjSub t L ≠ L := fun h' =>
      ht (CFSG.Quasithin.SBc13.mem_normalizer_of_conjSub_eq_self h')
    have hpair : ({L, CFSG.Quasithin.conjSub t L} : Set (Subgroup G)) ⊆ S := by
      intro x hx
      rcases hx with rfl | rfl
      exacts [hL, hLt]
    have hcard : S.ncard ≤ ({L, CFSG.Quasithin.conjSub t L} : Set (Subgroup G)).ncard := by
      rw [Set.ncard_pair hne.symm]
      exact h
    have hEq := Set.eq_of_subset_of_ncard_le hpair hcard (Set.toFinite S)
    intro z
    have hz : CFSG.Quasithin.conjSub z L ∈ S := ⟨z, rfl⟩
    rw [← hEq] at hz
    simpa using hz

end CFSG.LocalAnalysis.RankThreeUC.Section5
