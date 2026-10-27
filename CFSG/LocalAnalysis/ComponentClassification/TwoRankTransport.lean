module

public import CFSG.LocalAnalysis.ComponentClassification.Helpers
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.Defs

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoRankTransport

theorem bounded {G : Type*} [Group G] [Finite G] (subgroup : Subgroup G) :
    BddAbove {rank | ∃ elementary : Subgroup G, elementary ≤ subgroup ∧
      IsElemAbelian 2 elementary ∧ Nat.card elementary = 2 ^ rank} := by
  refine ⟨Nat.card G, ?_⟩
  rintro rank ⟨elementary, _, _, hcard⟩
  have hle := elementary.card_le_card_group
  rw [hcard] at hle
  exact (Nat.lt_two_pow_self (n := rank)).le.trans hle

theorem witness {G : Type*} [Group G] [Finite G] (subgroup : Subgroup G) :
    ∃ elementary : Subgroup G, elementary ≤ subgroup ∧ IsElemAbelian 2 elementary ∧
      Nat.card elementary = 2 ^ pRank 2 subgroup :=
  CFSG.SectionRank.exists_pRank one_lt_two subgroup

theorem rank_le {G : Type*} [Group G] [Finite G] (subgroup elementary : Subgroup G)
    (hle : elementary ≤ subgroup) (helementary : IsElemAbelian 2 elementary)
    (rank : ℕ) (hcard : Nat.card elementary = 2 ^ rank) : rank ≤ pRank 2 subgroup :=
  CFSG.SectionRank.le_pRank (by norm_num) hle helementary hcard

theorem elementary_map {G H : Type*} [Group G] [Group H]
    (homomorphism : G →* H) (subgroup : Subgroup G) (helementary : IsElemAbelian 2 subgroup) :
    IsElemAbelian 2 (subgroup.map homomorphism) := CFSG.Open.IsElemAbelian.map helementary _

theorem injective {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (homomorphism : G →* H) (hinjective : Function.Injective homomorphism) : twoRank G ≤ twoRank H := by
  obtain ⟨elementary, helementary, hcard⟩ := Helpers.twoRank_witness G
  apply rank_le (⊤ : Subgroup H) (elementary.map homomorphism) le_top
    (elementary_map homomorphism elementary helementary)
  rw [Subgroup.card_map_of_injective hinjective]
  exact hcard

theorem mono {G : Type*} [Group G] [Finite G] {first second : Subgroup G}
    (hle : first ≤ second) : pRank 2 first ≤ pRank 2 second :=
  CFSG.SectionRank.pRank_mono one_lt_two hle

theorem subgroup {G : Type*} [Group G] [Finite G] (subgroup : Subgroup G) :
    twoRank subgroup = pRank 2 subgroup :=
  (CFSG.SectionRank.pRank_eq_pRank_top_subgroup subgroup).symm

theorem equiv_map {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (subgroup : Subgroup G) (equivalence : G ≃* H) :
    pRank 2 (subgroup.map equivalence.toMonoidHom) = pRank 2 subgroup := by
  rw [← TwoRankTransport.subgroup, ← TwoRankTransport.subgroup]
  let restricted := subgroup.equivMapOfInjective equivalence.toMonoidHom equivalence.injective
  exact le_antisymm (injective restricted.symm.toMonoidHom restricted.symm.injective)
    (injective restricted.toMonoidHom restricted.injective)

end CFSG.ComponentClassification.TwoRankTransport
