module

public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictSylowIntersections
public import CFSG.LocalAnalysis.ComponentClassification.BlockSupport
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedOddIntersectionCommutator
public import CFSG.LocalAnalysis.ComponentClassification.ElementaryInvolutionExtension
public import CFSG.LocalAnalysis.ComponentClassification.ElementaryStrictActionRank

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockInvariantSupportRank

theorem not_invariant {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (rank : ℕ) (hpositive : 1 ≤ rank) (firstCommon secondCommon : Subgroup G)
    (hfirstProperties : BlockCommonInvolutionPackage.Common component
      ((UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) rank firstCommon)
    (hsecondProperties : BlockCommonInvolutionPackage.Common (UniversalOrbitBlock.conjugate component actor)
      (UniversalOrbitBlock.normalizer component) rank secondCommon)
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component)
    (member : UniversalOrbitBlock.generated (UniversalOrbitBlock.conjugate component actor))
    (hmember : member.val ∈ UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor)
    (horder : orderOf member.val = 2) (houtside : member.val ∉ secondCommon)
    (hnormalizes : member.val ∈ Subgroup.normalizer (first : Set G))
    (unused : Subgroup G) (hunused : unused ∈ UniversalOrbitBlock.block component)
    (hnot : UniversalOrbitBlock.conjugate unused actor ∉
      BlockSupport.support (UniversalOrbitBlock.conjugate component actor) member.val) :
    ¬ ∀ mover ∈ first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor),
      (fun factor => UniversalOrbitBlock.conjugate factor mover) ''
        BlockSupport.support (UniversalOrbitBlock.conjugate component actor) member.val =
          BlockSupport.support (UniversalOrbitBlock.conjugate component actor) member.val := by
  intro hinvariant
  let opposite := UniversalOrbitBlock.conjugate component actor
  let overlap := first ⊓ UniversalOrbitBlock.normalizer opposite
  let subset := BlockSupport.support opposite member.val
  let supported := BlockProperSupportOdd.subgroup opposite subset
  let acting := secondCommon ⊔ Subgroup.zpowers member.val
  have horbit := UniversalOrbitBlock.orbit_conjugate component component (UniversalOrbitBlock.mem_orbit_self component) actor
  have hevenOpposite := UniversalOrbitBlock.orbit_even component heven _ horbit
  have huniversalOpposite := UniversalOrbitBlock.orbit_universal component huniversal _ horbit
  have hquasisimpleOpposite := UniversalOrbitBlock.orbit_quasisimple component hquasisimple _ horbit
  have hsubset : subset ⊆ UniversalOrbitBlock.block opposite := BlockSupport.support_le _ _
  have hcommonContained : ∀ factor ∈ UniversalOrbitBlock.block component,
      secondCommon ≤ UniversalOrbitBlock.conjugate factor actor ⊓ UniversalOrbitBlock.normalizer component :=
    fun factor hfactor => hsecondProperties.contained _ ((OrbitBlockConjugation.block component factor actor).mpr hfactor)
  have hcommonProduct : secondCommon ≤ UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor :=
    ((hcommonContained second hsecond).trans inf_le_left).trans le_sup_left
  have hcommonCentralizes := MappedCenter.centralizes (UniversalOrbitBlock.generated opposite)
  have hcommutes : ∀ element ∈ secondCommon, Commute element member.val := by
    intro element helement
    exact (Subgroup.mem_centralizer_iff.mp (hcommonCentralizes (hsecondProperties.central helement))
      member.val member.property).symm
  obtain ⟨helementary, hsize⟩ := ElementaryInvolutionExtension.extend secondCommon hsecondProperties.isElementary
    rank hsecondProperties.card member.val horder houtside hcommutes
  have htwo : IsPGroup 2 acting := IsPGroup.of_card hsize
  have hproduct : acting ≤ UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor :=
    sup_le hcommonProduct (Subgroup.zpowers_le.mpr hmember)
  have hnormalizesFirst : acting ≤ Subgroup.normalizer (first : Set G) :=
    sup_le (BlockStrictSylowIntersections.right_common_normalizes component heven huniversal hcard hcontrol actor hactor
      secondCommon hsecondProperties.isElementary hcommonContained first hfirst) (Subgroup.zpowers_le.mpr hnormalizes)
  have hactingSupported : acting ≤ supported := by
    apply sup_le
    · exact hsecondProperties.central.trans le_sup_right
    · apply Subgroup.zpowers_le.mpr
      exact (BlockSupport.support_subproduct opposite hevenOpposite huniversalOpposite subset hsubset member).mp Set.Subset.rfl
  have hsupportedGenerated := BlockSupport.subgroup_le opposite subset hsubset
  have hsupportedNormalizer : supported ≤ UniversalOrbitBlock.normalizer opposite :=
    hsupportedGenerated.trans Subgroup.le_normalizer
  have hnormalizesOverlap : acting ≤ Subgroup.normalizer (overlap : Set G) :=
    SubgroupOddCoreNormalizer.inf first (UniversalOrbitBlock.normalizer opposite) acting hnormalizesFirst
      ((hactingSupported.trans hsupportedNormalizer).trans Subgroup.le_normalizer)
  have hsupportedInvariant : overlap ≤ Subgroup.normalizer (supported : Set G) :=
    BlockSupport.invariant_normalizes opposite hevenOpposite huniversalOpposite hquasisimpleOpposite
      subset hsubset overlap inf_le_right hinvariant
  have hodd : Odd (Nat.card ↥(first ⊓ supported)) := BlockProperSupportOdd.odd component heven huniversal hquasisimple hcard
    first hfirst actor hactor subset hsubset unused hunused hnot
  have hcommutator : ⁅acting, overlap⁆ ≤ (componentClassificationOddCore overlap).map overlap.subtype :=
    NormalizedOddIntersectionCommutator.le_core first supported (UniversalOrbitBlock.normalizer opposite) acting
      hsupportedNormalizer hactingSupported hnormalizesFirst hsupportedInvariant hodd
  have hdisjoint := BlockTwoActionFaithful.disjoint_factor component heven huniversal hquasisimple hcard
    first second third hfirst hsecond hthird actor hactor acting htwo hproduct
  have hcentralizers : ∀ element ∈ acting, element ≠ 1 → Subgroup.centralizer {element} ⊓ first ≤ overlap := by
    intro element helement hne central hcentral
    have hbound := BlockTwoActionFaithful.centralizer_le_image_normalizer component heven huniversal hquasisimple hcard
      second third hsecond hthird actor acting htwo hproduct element helement hne
    rw [OrbitBlockConjugation.normalizer] at hbound
    exact ⟨hcentral.2, hbound hcentral.1⟩
  have hstrict := BlockStrictSylowIntersections.forward component heven huniversal hquasisimple hcard hcontrol
    actor hactor rank hpositive firstCommon secondCommon hfirstProperties hsecondProperties first hfirst
  rw [OrbitBlockConjugation.normalizer] at hstrict
  have hrank := hfirstProperties.rank first hfirst
  rw [OrbitBlockConjugation.normalizer] at hrank
  have hbound := ElementaryStrictActionRank.bound first acting overlap (rank + 1) helementary hsize inf_le_left
    hdisjoint hnormalizesFirst hnormalizesOverlap hcentralizers hcommutator hstrict
  change rank + 1 ≤ pRank 2 (first ⊓ UniversalOrbitBlock.normalizer opposite) at hbound
  rw [hrank] at hbound
  omega

end CFSG.ComponentClassification.BlockInvariantSupportRank
