module

public import CFSG.CharacterTheory.TwoRankLowerBound.Helpers
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open

namespace CFSG.TwoRankLowerBound.Helpers

theorem isElemAbelian_map {G H : Type*} [Group G] [Group H]
    (elementary : Subgroup G) (helementary : IsElemAbelian 2 elementary)
    (homomorphism : G →* H) : IsElemAbelian 2 (elementary.map homomorphism) :=
  CFSG.Open.IsElemAbelian.map helementary _

theorem le_twoRank_of_injective {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (homomorphism : G →* H) (hinjective : Function.Injective homomorphism) :
    twoRank G ≤ twoRank H := by
  apply csSup_le'
  rintro rank ⟨elementary, _, helementary, hcard⟩
  apply le_twoRank_of_elementary H (elementary.map homomorphism)
    (isElemAbelian_map elementary helementary homomorphism) rank
  rw [Subgroup.card_map_of_injective hinjective, hcard]

theorem twoRank_subgroup_le {G : Type*} [Group G] [Finite G] (subgroup : Subgroup G) :
    twoRank subgroup ≤ twoRank G := by
  exact le_twoRank_of_injective subgroup.subtype Subtype.val_injective

end CFSG.TwoRankLowerBound.Helpers
