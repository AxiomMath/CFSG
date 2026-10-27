module

public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoActionFaithful
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionPrescribedSylowEmbedding
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedOddIntersectionCommutator
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeSupportInvariance

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockLargeProductAction

def support_union {G : Type*} [Group G] (component acting : Subgroup G) : Set (Subgroup G) :=
  ⋃ member : acting, BlockSupport.support component member.val

theorem commutator_le_core {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 5 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : second ≠ third)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (acting : Subgroup G) (htwo : IsPGroup 2 acting)
    (hproduct : acting ≤ UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor)
    (hnormalizes : acting ≤ Subgroup.normalizer (first : Set G)) :
    ⁅acting, first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor)⁆ ≤
      (componentClassificationOddCore ↥(first ⊓ UniversalOrbitBlock.normalizer
        (UniversalOrbitBlock.conjugate component actor))).map
          (first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor)).subtype := by
  let opposite := UniversalOrbitBlock.conjugate component actor
  let overlap := first ⊓ UniversalOrbitBlock.normalizer opposite
  let subset := support_union opposite acting
  let supported := BlockProperSupportOdd.subgroup opposite subset
  let pair := ({UniversalOrbitBlock.conjugate second actor, UniversalOrbitBlock.conjugate third actor} : Set (Subgroup G))
  have horbit := UniversalOrbitBlock.orbit_conjugate component component (UniversalOrbitBlock.mem_orbit_self component) actor
  have hevenOpposite := UniversalOrbitBlock.orbit_even component heven _ horbit
  have huniversalOpposite := UniversalOrbitBlock.orbit_universal component huniversal _ horbit
  have hquasisimpleOpposite := UniversalOrbitBlock.orbit_quasisimple component hquasisimple _ horbit
  have hproductGenerated : acting ≤ UniversalOrbitBlock.generated opposite := hproduct.trans
    (sup_le (CommutingComponentFamily.factor_le _ _ ((OrbitBlockConjugation.block component second actor).mpr hsecond))
      (CommutingComponentFamily.factor_le _ _ ((OrbitBlockConjugation.block component third actor).mpr hthird)))
  have hsubsetPair : subset ⊆ pair := by
    apply Set.iUnion_subset
    intro member
    exact BlockSupport.support_pair opposite hevenOpposite huniversalOpposite
      (UniversalOrbitBlock.conjugate second actor) (UniversalOrbitBlock.conjugate third actor)
        ((OrbitBlockConjugation.block component second actor).mpr hsecond)
        ((OrbitBlockConjugation.block component third actor).mpr hthird)
          ⟨member.val, hproductGenerated member.property⟩ (hproduct member.property)
  have hsubset : subset ⊆ UniversalOrbitBlock.block opposite := by
    apply Set.iUnion_subset
    intro member
    exact BlockSupport.support_le _ _
  have hinvariant : ∀ mover ∈ overlap,
      (fun factor => UniversalOrbitBlock.conjugate factor mover) '' subset = subset := by
    intro mover hmover
    change (fun factor => UniversalOrbitBlock.conjugate factor mover) ''
      (⋃ member : acting, BlockSupport.support opposite member.val) = _
    rw [Set.image_iUnion]
    apply congrArg (fun sets : acting → Set (Subgroup G) => ⋃ member, sets member)
    funext member
    obtain ⟨exponent, hpower⟩ := htwo member
    have hpowerAmbient : member.val ^ (2 ^ exponent) = 1 := congrArg Subtype.val hpower
    have htransport := BlockSupport.support_conjugate opposite hevenOpposite huniversalOpposite hquasisimpleOpposite
      mover hmover.2 member.val
    rw [← htransport]
    exact BlockLargeSupportInvariance.invariant component heven huniversal hquasisimple hcard first second third
      hfirst hsecond hthird hdistinct actor hactor ⟨member.val, hproductGenerated member.property⟩ exponent hpowerAmbient
        (hproduct member.property) (hnormalizes member.property) ⟨mover, hmover⟩
  have hsupportedInvariant : overlap ≤ Subgroup.normalizer (supported : Set G) :=
    BlockSupport.invariant_normalizes opposite hevenOpposite huniversalOpposite hquasisimpleOpposite
      subset hsubset overlap inf_le_right hinvariant
  have hactingSupported : acting ≤ supported := by
    intro member hmember
    exact (BlockSupport.support_subproduct opposite hevenOpposite huniversalOpposite subset hsubset
      ⟨member, hproductGenerated hmember⟩).mp (Set.subset_iUnion_of_subset (⟨member, hmember⟩ : acting) Set.Subset.rfl)
  have hsupportedNormalizer : supported ≤ UniversalOrbitBlock.normalizer opposite :=
    (BlockSupport.subgroup_le opposite subset hsubset).trans Subgroup.le_normalizer
  have hpair : pair.ncard = 2 := Set.ncard_pair
    (fun heq => hdistinct (Subgroup.map_injective (MulAut.conj actor).injective heq))
  have hsize : subset.ncard ≤ 2 := (Set.ncard_le_ncard hsubsetPair).trans_eq hpair
  have hambient : 5 ≤ (UniversalOrbitBlock.block opposite).ncard := by
    rw [FiniteSupportGeometry.ncard_eq, ← Nat.card_congr (OrbitBlockConjugation.equivalence component actor)]
    exact hcard
  have hnotSubset : ¬ UniversalOrbitBlock.block opposite ⊆ subset := by
    intro hcontained
    have hle := Set.ncard_le_ncard hcontained
    omega
  obtain ⟨unusedImage, hunusedImage, hnot⟩ := Set.not_subset.mp hnotSubset
  let unused := (OrbitBlockConjugation.equivalence component actor).symm ⟨unusedImage, hunusedImage⟩
  have hback : UniversalOrbitBlock.conjugate unused.val actor = unusedImage :=
    congrArg Subtype.val ((OrbitBlockConjugation.equivalence component actor).apply_symm_apply ⟨unusedImage, hunusedImage⟩)
  have hodd := BlockProperSupportOdd.odd component heven huniversal hquasisimple (by omega) first hfirst actor hactor
    subset hsubset unused.val unused.property (by rwa [hback])
  exact NormalizedOddIntersectionCommutator.le_core first supported (UniversalOrbitBlock.normalizer opposite)
    acting hsupportedNormalizer hactingSupported hnormalizes hsupportedInvariant hodd

theorem action {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 5 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : second ≠ third)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (acting : Subgroup G) (htwo : IsPGroup 2 acting)
    (hproduct : acting ≤ UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor)
    (hnormalizes : acting ≤ Subgroup.normalizer (first : Set G)) :
    let overlap := first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor)
    Disjoint first acting ∧ acting ≤ Subgroup.normalizer (overlap : Set G) ∧
      (∀ member ∈ acting, member ≠ 1 → Subgroup.centralizer {member} ⊓ first ≤ overlap) ∧
      ⁅acting, overlap⁆ ≤ (componentClassificationOddCore overlap).map overlap.subtype := by
  let opposite := UniversalOrbitBlock.conjugate component actor
  let overlap := first ⊓ UniversalOrbitBlock.normalizer opposite
  have hsmall : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component) := by omega
  have hproductGenerated : acting ≤ UniversalOrbitBlock.generated opposite := hproduct.trans
    (sup_le (CommutingComponentFamily.factor_le _ _ ((OrbitBlockConjugation.block component second actor).mpr hsecond))
      (CommutingComponentFamily.factor_le _ _ ((OrbitBlockConjugation.block component third actor).mpr hthird)))
  refine ⟨BlockTwoActionFaithful.disjoint_factor component heven huniversal hquasisimple hsmall
    first second third hfirst hsecond hthird actor hactor acting htwo hproduct, ?_, ?_,
    commutator_le_core component heven huniversal hquasisimple hcard first second third hfirst hsecond hthird
      hdistinct actor hactor acting htwo hproduct hnormalizes⟩
  · exact SubgroupOddCoreNormalizer.inf first (UniversalOrbitBlock.normalizer opposite) acting hnormalizes
      ((hproductGenerated.trans Subgroup.le_normalizer).trans Subgroup.le_normalizer)
  · intro member hmember hne central hcentral
    have hbound := BlockTwoActionFaithful.centralizer_le_image_normalizer component heven huniversal hquasisimple hsmall
      second third hsecond hthird actor acting htwo hproduct member hmember hne
    rw [OrbitBlockConjugation.normalizer] at hbound
    exact ⟨hcentral.2, hbound hcentral.1⟩

theorem embedding {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 5 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : second ≠ third)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (acting : Subgroup G) (htwo : IsPGroup 2 acting)
    (hproduct : acting ≤ UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor)
    (hnormalizes : acting ≤ Subgroup.normalizer (first : Set G))
    (hstrict : ∀ left : Sylow 2 ↥(first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor)),
      ∀ right : Sylow 2 first,
        Nat.card (left : Subgroup ↥(first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor))) <
          Nat.card (right : Subgroup first))
    (sylow : Sylow 2 ↥(first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor))) :
    ∃ homomorphism : acting →* Subgroup.center
      ((sylow : Subgroup ↥(first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor))).map
        (first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor)).subtype),
      Function.Injective homomorphism := by
  obtain ⟨hdisjoint, hnormalizesOverlap, hcentralizers, hcommutator⟩ := action component heven huniversal hquasisimple hcard
    first second third hfirst hsecond hthird hdistinct actor hactor acting htwo hproduct hnormalizes
  exact TwoActionPrescribedSylowEmbedding.embedding first acting _ inf_le_left htwo hdisjoint
    hnormalizes hnormalizesOverlap hcentralizers hcommutator hstrict sylow

end CFSG.ComponentClassification.BlockLargeProductAction
