module

public import CFSG.LocalAnalysis.ComponentClassification.TwoActionStrictEmbedding
public import CFSG.LocalAnalysis.ComponentClassification.TwoRankTransport

public section

open CFSG.Open

namespace CFSG.ComponentClassification.ElementaryStrictActionRank

theorem bound {G : Type*} [Group G] [Finite G]
    (ambient acting intersection : Subgroup G) (rank : ℕ)
    (helementary : IsElemAbelian 2 acting) (hcard : Nat.card acting = 2 ^ rank)
    (hintersection : intersection ≤ ambient) (hdisjoint : Disjoint ambient acting)
    (hnormalizesAmbient : acting ≤ Subgroup.normalizer (ambient : Set G))
    (hnormalizesIntersection : acting ≤ Subgroup.normalizer (intersection : Set G))
    (hcentralizers : ∀ member ∈ acting, member ≠ 1 →
      Subgroup.centralizer {member} ⊓ ambient ≤ intersection)
    (hcommutator : ⁅acting, intersection⁆ ≤ (componentClassificationOddCore intersection).map intersection.subtype)
    (hstrict : ∀ first : Sylow 2 intersection, ∀ second : Sylow 2 ambient,
      Nat.card (first : Subgroup intersection) < Nat.card (second : Subgroup ambient)) :
    rank ≤ pRank 2 intersection := by
  obtain ⟨sylow, homomorphism, hinjective⟩ := TwoActionStrictEmbedding.embedding ambient acting intersection
    hintersection (IsPGroup.of_card hcard) hdisjoint hnormalizesAmbient hnormalizesIntersection hcentralizers hcommutator hstrict
  let image := (sylow : Subgroup intersection).map intersection.subtype
  have himage : image ≤ intersection := Subgroup.map_subtype_le _
  have hbound := TwoRankTransport.injective ((Subgroup.center image).subtype.comp homomorphism)
    ((Subgroup.center image).subtype_injective.comp hinjective)
  rw [TwoRankTransport.subgroup acting, TwoRankTransport.subgroup image] at hbound
  exact (TwoRankTransport.rank_le acting acting le_rfl helementary rank hcard).trans
    (hbound.trans (TwoRankTransport.mono himage))

end CFSG.ComponentClassification.ElementaryStrictActionRank
