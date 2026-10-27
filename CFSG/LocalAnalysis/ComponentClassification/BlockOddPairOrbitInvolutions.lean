module

public import CFSG.LocalAnalysis.ComponentClassification.ElementarySylowControl
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictSylowIntersections
public import CFSG.LocalAnalysis.ComponentClassification.BlockOddPairOrbitEmbedding

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockOddPairOrbitInvolutions

theorem product_involution_normalizes {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (second third : Subgroup G)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component)
    (member : G) (hmember : member ∈ UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor)
    (horder : orderOf member = 2) (himage : member ∈ UniversalOrbitBlock.normalizer component) :
    ∀ first ∈ UniversalOrbitBlock.block component, member ∈ Subgroup.normalizer (first : Set G) := by
  have hmap : member ∈ (second ⊔ third).map (MulAut.conj actor).toMonoidHom := by
    rw [Subgroup.map_sup]
    exact hmember
  obtain ⟨original, horiginal, heq⟩ := Subgroup.mem_map.mp hmap
  have horiginalOrder : orderOf original = 2 :=
    (orderOf_injective (MulAut.conj actor).toMonoidHom (MulAut.conj actor).injective original).symm.trans
      ((congrArg orderOf heq).trans horder)
  have hfusion := BlockProductFusion.product_involution_mem component heven huniversal hcard second third hsecond hthird
    original horiginal horiginalOrder
  have himageOriginal : (MulAut.conj actor) original ∈ UniversalOrbitBlock.normalizer component := by
    change (MulAut.conj actor).toMonoidHom original ∈ UniversalOrbitBlock.normalizer component
    rwa [heq]
  intro first hfirst
  have hfixed := hcontrol original hfusion actor hactor himageOriginal first hfirst
  have heq' : (MulAut.conj actor) original = member := heq
  rw [heq'] at hfixed
  exact (CommutingComponentFamily.normalizer_iff_conjugate_eq _ member).mpr hfixed

theorem normalizer {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : second ≠ third)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (rank : ℕ) (elementary : Subgroup G)
    (properties : BlockCommonInvolutionPackage.Common (UniversalOrbitBlock.conjugate component actor)
      (UniversalOrbitBlock.normalizer component) rank elementary)
    (hrank : pRank 2 (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) = rank)
    (hoddOrbit : Odd (Nat.card ↥(ConjugationPairStabilizer.orbit
      (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)
        (UniversalOrbitBlock.conjugate second actor) (UniversalOrbitBlock.conjugate third actor))))
    (hstrict : ∀ left : Sylow 2 ↥(first ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom), ∀ right : Sylow 2 first,
        Nat.card (left : Subgroup ↥(first ⊓
          (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) <
            Nat.card (right : Subgroup first)) :
    let opposite := UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor
    let normalizer := opposite ⊓ Subgroup.normalizer (first : Set G)
    pRank 2 normalizer = rank ∧
      (∀ sylow : Sylow 2 normalizer,
        IsMulCommutative ((sylow : Subgroup normalizer).map normalizer.subtype) ∧
        InvolutionGeneratedSubgroup.omega ((sylow : Subgroup normalizer).map normalizer.subtype) = elementary) ∧
      (∀ member : G, member ∈ normalizer ∧ orderOf member = 2 ↔ member ∈ elementary ∧ member ≠ 1) := by
  let oppositeFirst := UniversalOrbitBlock.conjugate second actor
  let oppositeSecond := UniversalOrbitBlock.conjugate third actor
  let opposite := oppositeFirst ⊔ oppositeSecond
  let normalizer := opposite ⊓ Subgroup.normalizer (first : Set G)
  let intersection := first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom
  let prescribed : Sylow 2 intersection := Classical.choice inferInstance
  have hcontained : ∀ factor ∈ UniversalOrbitBlock.block component,
      elementary ≤ UniversalOrbitBlock.conjugate factor actor ⊓ UniversalOrbitBlock.normalizer component :=
    fun factor hfactor => properties.contained _ ((OrbitBlockConjugation.block component factor actor).mpr hfactor)
  have helementaryNormalizes := BlockStrictSylowIntersections.right_common_normalizes component heven huniversal hcard hcontrol
    actor hactor elementary properties.isElementary hcontained first hfirst
  have helementaryNormalizer : elementary ≤ normalizer :=
    le_inf (((hcontained second hsecond).trans inf_le_left).trans le_sup_left) helementaryNormalizes
  have helementaryCentral : elementary ≤ Subgroup.centralizer (normalizer : Set G) := by
    have hfactors := BlockCommonInvolutionPair.image_centralizes component heven huniversal hcard actor elementary
      (fun factor hfactor => (hcontained factor hfactor).trans inf_le_left)
    have hoppositeCentral : opposite ≤ Subgroup.centralizer (elementary : Set G) := sup_le
      (Subgroup.le_centralizer_iff.mp (hfactors second hsecond)) (Subgroup.le_centralizer_iff.mp (hfactors third hthird))
    exact Subgroup.le_centralizer_iff.mp (inf_le_left.trans hoppositeCentral)
  have hsylows : ∀ sylow : Sylow 2 normalizer,
      IsMulCommutative ((sylow : Subgroup normalizer).map normalizer.subtype) ∧
      pRank 2 ((sylow : Subgroup normalizer).map normalizer.subtype) ≤ rank := by
    intro sylow
    let image := (sylow : Subgroup normalizer).map normalizer.subtype
    have himage : image ≤ normalizer := by
      rintro member ⟨lift, hlift, rfl⟩
      exact lift.property
    obtain ⟨hab, homomorphism, hinjective⟩ := BlockOddPairOrbitEmbedding.embedding component heven huniversal hquasisimple
      hcard first second third hfirst hsecond hthird hdistinct actor hactor image
        (sylow.isPGroup'.map normalizer.subtype) (himage.trans inf_le_left) (himage.trans inf_le_right)
          hoddOrbit hstrict prescribed
    have hprescribedImage : (prescribed : Subgroup intersection).map intersection.subtype ≤ intersection := by
      rintro member ⟨lift, hlift, rfl⟩
      exact lift.property
    let inclusion := (Subgroup.inclusion hprescribedImage).comp
      (Subgroup.center ((prescribed : Subgroup intersection).map intersection.subtype)).subtype
    have hinclusion : Function.Injective inclusion :=
      (Subgroup.inclusion_injective hprescribedImage).comp (Subgroup.center _).subtype_injective
    have hbound := TwoRankTransport.injective (inclusion.comp homomorphism) (hinclusion.comp hinjective)
    rw [TwoRankTransport.subgroup, TwoRankTransport.subgroup, hrank] at hbound
    exact ⟨hab, hbound⟩
  have homega : ∀ sylow : Sylow 2 normalizer,
      InvolutionGeneratedSubgroup.omega ((sylow : Subgroup normalizer).map normalizer.subtype) = elementary := by
    intro sylow
    exact ElementarySylowControl.omega normalizer elementary properties.isElementary helementaryNormalizer
      helementaryCentral rank properties.card sylow (hsylows sylow).1 (hsylows sylow).2
  have hnormalizerRank : pRank 2 normalizer = rank := by
    apply le_antisymm
    · let sylow : Sylow 2 normalizer := Classical.choice inferInstance
      have hbound := (hsylows sylow).2
      rwa [InvolutionGeneratedSubgroup.sylow_rank_eq] at hbound
    · exact TwoRankTransport.rank_le normalizer elementary helementaryNormalizer properties.isElementary rank properties.card
  exact ⟨hnormalizerRank, fun sylow => ⟨(hsylows sylow).1, homega sylow⟩,
    ElementarySylowControl.involutions normalizer elementary properties.isElementary helementaryNormalizer homega⟩

theorem product_intersection {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : second ≠ third)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (rank : ℕ) (elementary : Subgroup G)
    (properties : BlockCommonInvolutionPackage.Common (UniversalOrbitBlock.conjugate component actor)
      (UniversalOrbitBlock.normalizer component) rank elementary)
    (hrank : pRank 2 (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) = rank)
    (hoddOrbit : Odd (Nat.card ↥(ConjugationPairStabilizer.orbit
      (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)
        (UniversalOrbitBlock.conjugate second actor) (UniversalOrbitBlock.conjugate third actor))))
    (hstrict : ∀ left : Sylow 2 ↥(first ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom), ∀ right : Sylow 2 first,
        Nat.card (left : Subgroup ↥(first ⊓
          (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) <
            Nat.card (right : Subgroup first))
    (member : G) :
    member ∈ (UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor) ⊓
      UniversalOrbitBlock.normalizer component ∧ orderOf member = 2 ↔ member ∈ elementary ∧ member ≠ 1 := by
  have hnormalizer := normalizer component heven huniversal hquasisimple hcard hcontrol first second third hfirst hsecond hthird
    hdistinct actor hactor rank elementary properties hrank hoddOrbit hstrict
  constructor
  · rintro ⟨hmember, horder⟩
    have hnormalizes := product_involution_normalizes component heven huniversal hcard hcontrol actor hactor second third
      hsecond hthird member hmember.1 horder hmember.2 first hfirst
    exact (hnormalizer.2.2 member).mp ⟨⟨hmember.1, hnormalizes⟩, horder⟩
  · rintro ⟨hmember, hne⟩
    have hbase := properties.contained _ ((OrbitBlockConjugation.block component second actor).mpr hsecond) hmember
    exact ⟨⟨(le_sup_left : UniversalOrbitBlock.conjugate second actor ≤
      UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor) hbase.1, hbase.2⟩,
        orderOf_eq_prime (properties.isElementary.2 member hmember) hne⟩

theorem even_orbit_of_extra_involution {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : second ≠ third)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (rank : ℕ) (elementary : Subgroup G)
    (properties : BlockCommonInvolutionPackage.Common (UniversalOrbitBlock.conjugate component actor)
      (UniversalOrbitBlock.normalizer component) rank elementary)
    (hrank : pRank 2 (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) = rank)
    (hstrict : ∀ left : Sylow 2 ↥(first ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom), ∀ right : Sylow 2 first,
        Nat.card (left : Subgroup ↥(first ⊓
          (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) <
            Nat.card (right : Subgroup first))
    (member : G)
    (hmember : member ∈ (UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor) ⊓
      UniversalOrbitBlock.normalizer component) (horder : orderOf member = 2) (hextra : member ∉ elementary) :
    Even (Nat.card ↥(ConjugationPairStabilizer.orbit
      (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)
        (UniversalOrbitBlock.conjugate second actor) (UniversalOrbitBlock.conjugate third actor))) := by
  apply Nat.not_odd_iff_even.mp
  intro hodd
  exact hextra ((product_intersection component heven huniversal hquasisimple hcard hcontrol first second third
    hfirst hsecond hthird hdistinct actor hactor rank elementary properties hrank hodd hstrict member).mp ⟨hmember, horder⟩).1

end CFSG.ComponentClassification.BlockOddPairOrbitInvolutions
