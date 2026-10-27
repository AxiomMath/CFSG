module

public import CFSG.Mathlib.GroupTheory.Basic
public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open

namespace CFSG.TwoRankLowerBound.Helpers

theorem twoRank_bddAbove (G : Type*) [Group G] [Finite G] :
    BddAbove {rank | ∃ elementary : Subgroup G,
      elementary ≤ ⊤ ∧ IsElemAbelian 2 elementary ∧ Nat.card elementary = 2 ^ rank} := by
  refine ⟨Nat.card G, ?_⟩
  rintro rank ⟨elementary, _, _, hcard⟩
  exact (Nat.le_of_lt Nat.lt_two_pow_self).trans
    (hcard ▸ elementary.card_le_card_group)

theorem le_twoRank_of_elementary (G : Type*) [Group G] [Finite G]
    (elementary : Subgroup G) (helementary : IsElemAbelian 2 elementary)
    (rank : ℕ) (hcard : Nat.card elementary = 2 ^ rank) : rank ≤ twoRank G := by
  exact le_csSup (twoRank_bddAbove G) ⟨elementary, le_top, helementary, hcard⟩

theorem not_isMulCommutative_of_nonabelian (G : Type*) [Group G]
    (hnonabelian : ∃ left right : G, left * right ≠ right * left) :
    ¬IsMulCommutative G := by
  intro hcommutative
  obtain ⟨left, right, hne⟩ := hnonabelian
  exact hne (isMulCommutative_iff.mp hcommutative left right)

theorem perfect_of_nonabelian_simple (G : Type*) [Group G] [IsSimpleGroup G]
    (hnonabelian : ∃ left right : G, left * right ≠ right * left) :
    Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases CFSG.eq_bot_or_eq_top_of_normal (commutator G) inferInstance with
    htrivial | hwhole
  · exact False.elim (not_isMulCommutative_of_nonabelian G hnonabelian
      ((commutator_eq_bot_iff G).mp htrivial))
  · exact hwhole

theorem center_eq_bot_of_nonabelian_simple (G : Type*) [Group G] [IsSimpleGroup G]
    (hnonabelian : ∃ left right : G, left * right ≠ right * left) :
    Subgroup.center G = ⊥ := by
  rcases CFSG.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with
    htrivial | hwhole
  · exact htrivial
  · exact False.elim (not_isMulCommutative_of_nonabelian G hnonabelian
      (Subgroup.center_eq_top_iff.mp hwhole))

theorem exists_involution_of_even_card (G : Type*) [Group G] [Finite G]
    (heven : Even (Nat.card G)) : ∃ involution : G, orderOf involution = 2 := by
  exact exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)

theorem ker_eq_top_of_perfect (G A : Type*) [Group G] [CommGroup A] [Group.IsPerfect G]
    (homomorphism : G →* A) : homomorphism.ker = ⊤ := by
  apply top_unique
  calc
    ⊤ = commutator G := Group.IsPerfect.commutator_eq_top.symm
    _ ≤ homomorphism.ker := Abelianization.commutator_subset_ker homomorphism

theorem sylow_two_not_isCyclic_of_perfect (G : Type*) [Group G] [Finite G]
    [Group.IsPerfect G] (heven : Even (Nat.card G)) (sylow : Sylow 2 G) :
    ¬IsCyclic (sylow : Subgroup G) := by
  intro hcyclic
  have : IsCyclic (sylow : Subgroup G) := hcyclic
  let : CommGroup (sylow : Subgroup G) := IsCyclic.commGroup
  have hnormalizer : Subgroup.normalizer (sylow : Set G) ≤
      Subgroup.centralizer (sylow : Set G) :=
    IsCyclic.normalizer_le_centralizer
      ((Nat.minFac_eq_two_iff _).mpr (even_iff_two_dvd.mp heven)) hcyclic
  let transfer : G →* (sylow : Subgroup G) := MonoidHom.transferSylow sylow hnormalizer
  have hkernel : transfer.ker = ⊤ := ker_eq_top_of_perfect G (sylow : Subgroup G) transfer
  have hcomplement := MonoidHom.ker_transferSylow_isComplement' sylow hnormalizer
  change transfer.ker.IsComplement' (sylow : Subgroup G) at hcomplement
  rw [hkernel] at hcomplement
  exact sylow.ne_bot_of_dvd_card (even_iff_two_dvd.mp heven)
    (Subgroup.isComplement'_top_left.mp hcomplement)

theorem sylow_two_not_isCyclic_of_nonabelian_simple (G : Type*) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonabelian : ∃ left right : G, left * right ≠ right * left)
    (heven : Even (Nat.card G)) (sylow : Sylow 2 G) :
    ¬IsCyclic (sylow : Subgroup G) := by
  have := perfect_of_nonabelian_simple G hnonabelian
  exact sylow_two_not_isCyclic_of_perfect G heven sylow

end CFSG.TwoRankLowerBound.Helpers
