module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_mem_normalizer_not_mem_of_lt_pGroup {Q S : Subgroup G} (hS : IsPGroup p S)
    (hQS : Q < S) : ∃ z ∈ S, z ∉ Q ∧ z ∈ normalizer (Q : Set G) := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : Q.subgroupOf S < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hQS.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : S) ∈ Q.subgroupOf S := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyQ⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := S) _ hlt)
  refine ⟨y, y.2, fun h => hyQ (mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (normalizer (Q : Set G)).subgroupOf S := by
    rw [subgroupOf_normalizer_eq hQS.le]
    exact hyN
  exact mem_subgroupOf.mp hy

theorem exists_sylow_eq_of_normalizer_le {Q N : Subgroup G} (hQ : IsPGroup p Q)
    (hmax : ∀ K : Subgroup G, IsPGroup p K → Q ≤ K → K ≤ N → K ≤ Q)
    (hN : ∀ z ∈ normalizer (Q : Set G), (∃ n : ℕ, z ^ p ^ n = 1) → z ∈ N) :
    ∃ S : Sylow p G, (S : Subgroup G) = Q := by
  obtain ⟨S, hQS⟩ := hQ.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  have hlt : Q < S := lt_of_le_of_ne hQS (Ne.symm hne)
  obtain ⟨z, hzS, hzQ, hzN⟩ := exists_mem_normalizer_not_mem_of_lt_pGroup S.isPGroup' hlt
  have hKp : IsPGroup p (S ⊓ normalizer (Q : Set G) : Subgroup G) :=
    S.isPGroup'.to_le inf_le_left
  have hKN : (S ⊓ normalizer (Q : Set G) : Subgroup G) ≤ N := by
    intro x hx
    obtain ⟨n, hn⟩ := hKp ⟨x, hx⟩
    refine hN x (mem_inf.mp hx).2 ⟨n, ?_⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hK := hmax (S ⊓ normalizer (Q : Set G)) hKp (le_inf hQS le_normalizer) hKN
  exact hzQ (hK (mem_inf.mpr ⟨hzS, hzN⟩))

end CFSG.SeitzReduction.RankOne
