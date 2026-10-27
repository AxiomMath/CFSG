module

public import CFSG.LocalAnalysis.ComponentClassification.BlockOddPairOrbitInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductAction

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockLargeProductInvolutions

theorem normalizer {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 5 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : second ≠ third)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (rank : ℕ) (elementary : Subgroup G)
    (properties : BlockCommonInvolutionPackage.Common (UniversalOrbitBlock.conjugate component actor)
      (UniversalOrbitBlock.normalizer component) rank elementary)
    (hrank : pRank 2 (first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor)) = rank)
    (hstrict : ∀ left : Sylow 2 ↥(first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor)),
      ∀ right : Sylow 2 first,
        Nat.card (left : Subgroup ↥(first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor))) <
          Nat.card (right : Subgroup first)) :
    let product := UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor
    let normalizer := product ⊓ Subgroup.normalizer (first : Set G)
    pRank 2 normalizer = rank ∧
      (∀ sylow : Sylow 2 normalizer,
        IsMulCommutative ((sylow : Subgroup normalizer).map normalizer.subtype) ∧
          pRank 2 ((sylow : Subgroup normalizer).map normalizer.subtype) = rank ∧
          InvolutionGeneratedSubgroup.omega ((sylow : Subgroup normalizer).map normalizer.subtype) = elementary) ∧
      (∀ member : G, member ∈ normalizer ∧ orderOf member = 2 ↔ member ∈ elementary ∧ member ≠ 1) := by
  let product := UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor
  let normalizer := product ⊓ Subgroup.normalizer (first : Set G)
  let overlap := first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor)
  let prescribed : Sylow 2 overlap := Classical.choice inferInstance
  have hsmall : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component) := by omega
  have hcontained : ∀ factor ∈ UniversalOrbitBlock.block component,
      elementary ≤ UniversalOrbitBlock.conjugate factor actor ⊓ UniversalOrbitBlock.normalizer component :=
    fun factor hfactor => properties.contained _ ((OrbitBlockConjugation.block component factor actor).mpr hfactor)
  have helementaryNormalizes := BlockStrictSylowIntersections.right_common_normalizes component heven huniversal hsmall hcontrol
    actor hactor elementary properties.isElementary hcontained first hfirst
  have helementaryNormalizer : elementary ≤ normalizer :=
    le_inf (((hcontained second hsecond).trans inf_le_left).trans le_sup_left) helementaryNormalizes
  have helementaryCentral : elementary ≤ Subgroup.centralizer (normalizer : Set G) := by
    have hfactors := BlockCommonInvolutionPair.image_centralizes component heven huniversal hsmall actor elementary
      (fun factor hfactor => (hcontained factor hfactor).trans inf_le_left)
    have hproductCentral : product ≤ Subgroup.centralizer (elementary : Set G) := sup_le
      (Subgroup.le_centralizer_iff.mp (hfactors second hsecond)) (Subgroup.le_centralizer_iff.mp (hfactors third hthird))
    exact Subgroup.le_centralizer_iff.mp (inf_le_left.trans hproductCentral)
  have hsylows : ∀ sylow : Sylow 2 normalizer,
      IsMulCommutative ((sylow : Subgroup normalizer).map normalizer.subtype) ∧
        pRank 2 ((sylow : Subgroup normalizer).map normalizer.subtype) ≤ rank := by
    intro sylow
    let image := (sylow : Subgroup normalizer).map normalizer.subtype
    have himage : image ≤ normalizer := Subgroup.map_subtype_le _
    obtain ⟨homomorphism, hinjective⟩ := BlockLargeProductAction.embedding component heven huniversal hquasisimple
      hcard first second third hfirst hsecond hthird hdistinct actor hactor image
        (sylow.isPGroup'.map normalizer.subtype) (himage.trans inf_le_left) (himage.trans inf_le_right) hstrict prescribed
    have hab := TwoActionDisplacementEmbedding.abelian_of_embedding homomorphism hinjective
    have hprescribed : (prescribed : Subgroup overlap).map overlap.subtype ≤ overlap := Subgroup.map_subtype_le _
    let inclusion := (Subgroup.inclusion hprescribed).comp
      (Subgroup.center ((prescribed : Subgroup overlap).map overlap.subtype)).subtype
    have hinclusion : Function.Injective inclusion :=
      (Subgroup.inclusion_injective hprescribed).comp (Subgroup.center _).subtype_injective
    have hbound := TwoRankTransport.injective (inclusion.comp homomorphism) (hinclusion.comp hinjective)
    rw [TwoRankTransport.subgroup, TwoRankTransport.subgroup, hrank] at hbound
    exact ⟨hab, hbound⟩
  have homega : ∀ sylow : Sylow 2 normalizer,
      InvolutionGeneratedSubgroup.omega ((sylow : Subgroup normalizer).map normalizer.subtype) = elementary := by
    intro sylow
    exact ElementarySylowControl.omega normalizer elementary properties.isElementary helementaryNormalizer
      helementaryCentral rank properties.card sylow (hsylows sylow).1 (hsylows sylow).2
  have hsylowRank : ∀ sylow : Sylow 2 normalizer,
      pRank 2 ((sylow : Subgroup normalizer).map normalizer.subtype) = rank := by
    intro sylow
    exact le_antisymm (hsylows sylow).2 (TwoRankTransport.rank_le _ elementary
      (ElementarySylowControl.contained_every_sylow normalizer elementary properties.isElementary
        helementaryNormalizer helementaryCentral sylow) properties.isElementary rank properties.card)
  have hnormalizerRank : pRank 2 normalizer = rank := by
    let sylow : Sylow 2 normalizer := Classical.choice inferInstance
    have heq := hsylowRank sylow
    rwa [InvolutionGeneratedSubgroup.sylow_rank_eq] at heq
  exact ⟨hnormalizerRank, fun sylow => ⟨(hsylows sylow).1, hsylowRank sylow, homega sylow⟩,
    ElementarySylowControl.involutions normalizer elementary properties.isElementary helementaryNormalizer homega⟩

theorem product_intersection {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 5 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : second ≠ third)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (rank : ℕ) (elementary : Subgroup G)
    (properties : BlockCommonInvolutionPackage.Common (UniversalOrbitBlock.conjugate component actor)
      (UniversalOrbitBlock.normalizer component) rank elementary)
    (hrank : pRank 2 (first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor)) = rank)
    (hstrict : ∀ left : Sylow 2 ↥(first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor)),
      ∀ right : Sylow 2 first,
        Nat.card (left : Subgroup ↥(first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor))) <
          Nat.card (right : Subgroup first))
    (member : G) :
    member ∈ (UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor) ⊓
      UniversalOrbitBlock.normalizer component ∧ orderOf member = 2 ↔ member ∈ elementary ∧ member ≠ 1 := by
  have hnormalizer := normalizer component heven huniversal hquasisimple hcard hcontrol first second third hfirst hsecond hthird
    hdistinct actor hactor rank elementary properties hrank hstrict
  constructor
  · rintro ⟨hmember, horder⟩
    have hnormalizes := BlockOddPairOrbitInvolutions.product_involution_normalizes component heven huniversal (by omega)
      hcontrol actor hactor second third hsecond hthird member hmember.1 horder hmember.2 first hfirst
    exact (hnormalizer.2.2 member).mp ⟨⟨hmember.1, hnormalizes⟩, horder⟩
  · rintro ⟨hmember, hne⟩
    have hcontained := properties.contained (UniversalOrbitBlock.conjugate second actor)
      ((OrbitBlockConjugation.block component second actor).mpr hsecond) hmember
    exact ⟨⟨(le_sup_left : UniversalOrbitBlock.conjugate second actor ≤
      UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor) hcontained.1, hcontained.2⟩,
      orderOf_eq_prime (properties.isElementary.2 member hmember) hne⟩

theorem exact_involutions {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 5 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (rank : ℕ) (hpositive : 1 ≤ rank) (firstCommon secondCommon : Subgroup G)
    (hfirstProperties : BlockCommonInvolutionPackage.Common component
      ((UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) rank firstCommon)
    (hsecondProperties : BlockCommonInvolutionPackage.Common (UniversalOrbitBlock.conjugate component actor)
      (UniversalOrbitBlock.normalizer component) rank secondCommon)
    (second third : Subgroup G) (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : second ≠ third) (member : G) :
    member ∈ (UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor) ⊓
      UniversalOrbitBlock.normalizer component ∧ orderOf member = 2 ↔ member ∈ secondCommon ∧ member ≠ 1 := by
  have hfirst := UniversalOrbitBlock.mem_block_self component
  have hrank := hfirstProperties.rank component hfirst
  have hstrict := BlockStrictSylowIntersections.forward component heven huniversal hquasisimple (by omega) hcontrol
    actor hactor rank hpositive firstCommon secondCommon hfirstProperties hsecondProperties component hfirst
  rw [OrbitBlockConjugation.normalizer] at hrank hstrict
  exact product_intersection component heven huniversal hquasisimple hcard hcontrol component second third hfirst hsecond hthird
    hdistinct actor hactor rank secondCommon hsecondProperties hrank hstrict member

end CFSG.ComponentClassification.BlockLargeProductInvolutions
