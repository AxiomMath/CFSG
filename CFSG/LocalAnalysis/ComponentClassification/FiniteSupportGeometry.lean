module

public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.FiniteSupportGeometry

theorem ncard_eq {Index : Type*} [Finite Index] (subset : Set Index) : subset.ncard = Nat.card subset := by
  classical
  let : Fintype subset := Fintype.ofFinite _
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, Nat.card_eq_fintype_card]

theorem cover_pair {Index : Type*} [Finite Index] (ambient pair support moved : Set Index)
    (hambient : ambient.ncard = 4) (hpair : pair.ncard = 2)
    (hsupport : support ⊆ pair) (hmoved : moved ⊆ ambient)
    (hcard : moved.ncard = support.ncard) (hcover : support ∪ moved = ambient) :
    support = pair ∧ moved = ambient \ pair := by
  have hupper := Set.ncard_le_ncard hsupport
  have hsum := Set.ncard_union_le support moved
  rw [hcover, hambient, hcard] at hsum
  have hsize : support.ncard = 2 := by omega
  have heq : support = pair := Set.eq_of_subset_of_ncard_le hsupport (by omega)
  have hdisjoint : Disjoint support moved := by
    by_contra hnot
    have hlt := Set.ncard_union_lt (s := support) (t := moved) (Set.toFinite support) (Set.toFinite moved) hnot
    rw [hcover, hambient, hcard, hsize] at hlt
    omega
  refine ⟨heq, ?_⟩
  ext point
  constructor
  · intro hpoint
    refine ⟨hmoved hpoint, ?_⟩
    intro hpointPair
    exact Set.disjoint_left.mp hdisjoint (heq ▸ hpointPair) hpoint
  · intro hpoint
    have hpointCover : point ∈ support ∪ moved := hcover.symm ▸ hpoint.1
    rcases hpointCover with hpointSupport | hpointMoved
    · exact (hpoint.2 (heq ▸ hpointSupport)).elim
    · exact hpointMoved

theorem exists_unused {Index : Type*} [Finite Index] (ambient pair : Set Index)
    (hambient : ambient.ncard = 4) (hpair : pair.ncard = 2) :
    ∃ point ∈ ambient, point ∉ pair := by
  by_contra hnot
  have hsubset : ambient ⊆ pair := by
    intro point hpoint
    by_contra hpointNot
    exact hnot ⟨point, hpoint, hpointNot⟩
  have hle := Set.ncard_le_ncard hsubset
  rw [hambient, hpair] at hle
  omega

end CFSG.ComponentClassification.FiniteSupportGeometry
