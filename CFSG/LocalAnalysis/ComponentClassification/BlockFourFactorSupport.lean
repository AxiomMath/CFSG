module

public import CFSG.LocalAnalysis.ComponentClassification.BlockOddPairOrbitInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockSupportDisplacement
public import CFSG.LocalAnalysis.ComponentClassification.BlockInvariantSupportRank
public import CFSG.LocalAnalysis.ComponentClassification.FiniteSupportGeometry

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockFourFactorSupport

structure Context {G : Type*} [Group G] [Finite G] (component : Subgroup G) (actor : G)
    (rank : ℕ) (firstCommon secondCommon second third : Subgroup G)
    (member : UniversalOrbitBlock.generated (UniversalOrbitBlock.conjugate component actor)) : Prop where
  even : Even (Nat.card component)
  universal : UniversalComponentBlock.Universal component
  quasisimple : IsQuasisimple component
  four : Nat.card ↥(UniversalOrbitBlock.block component) = 4
  control : BlockFactorContainment.ExternalControl component
  outside : actor ∉ UniversalOrbitBlock.normalizer component
  positive : 1 ≤ rank
  original : BlockCommonInvolutionPackage.Common component
    ((UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) rank firstCommon
  opposite : BlockCommonInvolutionPackage.Common (UniversalOrbitBlock.conjugate component actor)
    (UniversalOrbitBlock.normalizer component) rank secondCommon
  second_mem : second ∈ UniversalOrbitBlock.block component
  third_mem : third ∈ UniversalOrbitBlock.block component
  distinct : second ≠ third
  product : member.val ∈ UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor
  involution : orderOf member.val = 2
  external_mem : member.val ∈ UniversalOrbitBlock.normalizer component
  not_common : member.val ∉ secondCommon

theorem Context.geometry {G : Type*} [Group G] [Finite G]
    {component : Subgroup G} {actor : G} {rank : ℕ} {firstCommon secondCommon second third : Subgroup G}
    {member : UniversalOrbitBlock.generated (UniversalOrbitBlock.conjugate component actor)}
    (context : Context component actor rank firstCommon secondCommon second third member)
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component) :
    let opposite := UniversalOrbitBlock.conjugate component actor
    let pair := ({UniversalOrbitBlock.conjugate second actor, UniversalOrbitBlock.conjugate third actor} : Set (Subgroup G))
    BlockSupport.support opposite member.val = pair ∧
      (∀ mover : ↥(first ⊓ UniversalOrbitBlock.normalizer opposite),
        BlockSupport.support opposite ((MulAut.conj mover.val) member.val) = pair ∨
          BlockSupport.support opposite ((MulAut.conj mover.val) member.val) = UniversalOrbitBlock.block opposite \ pair) ∧
      ∃ mover : ↥(first ⊓ UniversalOrbitBlock.normalizer opposite),
        BlockSupport.support opposite ((MulAut.conj mover.val) member.val) = UniversalOrbitBlock.block opposite \ pair := by
  let opposite := UniversalOrbitBlock.conjugate component actor
  let pair := ({UniversalOrbitBlock.conjugate second actor, UniversalOrbitBlock.conjugate third actor} : Set (Subgroup G))
  let support := BlockSupport.support opposite member.val
  have hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component) := by rw [context.four]; omega
  have horbit := UniversalOrbitBlock.orbit_conjugate component component (UniversalOrbitBlock.mem_orbit_self component) actor
  have hevenOpposite := UniversalOrbitBlock.orbit_even component context.even _ horbit
  have huniversalOpposite := UniversalOrbitBlock.orbit_universal component context.universal _ horbit
  have hquasisimpleOpposite := UniversalOrbitBlock.orbit_quasisimple component context.quasisimple _ horbit
  have hpair : pair.ncard = 2 := Set.ncard_pair
    (fun heq => context.distinct (Subgroup.map_injective (MulAut.conj actor).injective heq))
  have hambient : (UniversalOrbitBlock.block opposite).ncard = 4 := by
    rw [FiniteSupportGeometry.ncard_eq, ← Nat.card_congr (OrbitBlockConjugation.equivalence component actor), context.four]
  have hsupportPair : support ⊆ pair := BlockSupport.support_pair opposite hevenOpposite huniversalOpposite
    (UniversalOrbitBlock.conjugate second actor) (UniversalOrbitBlock.conjugate third actor)
      ((OrbitBlockConjugation.block component second actor).mpr context.second_mem)
      ((OrbitBlockConjugation.block component third actor).mpr context.third_mem) member context.product
  obtain ⟨unusedImage, hunusedImage, hnotPair⟩ := FiniteSupportGeometry.exists_unused
    (UniversalOrbitBlock.block opposite) pair hambient hpair
  let unused := (OrbitBlockConjugation.equivalence component actor).symm ⟨unusedImage, hunusedImage⟩
  have hunusedBack : UniversalOrbitBlock.conjugate unused.val actor = unusedImage :=
    congrArg Subtype.val ((OrbitBlockConjugation.equivalence component actor).apply_symm_apply ⟨unusedImage, hunusedImage⟩)
  have hnormalizes := BlockOddPairOrbitInvolutions.product_involution_normalizes component context.even context.universal hcard
    context.control actor context.outside second third context.second_mem context.third_mem member.val context.product
      context.involution context.external_mem first hfirst
  have hnotInvariant := BlockInvariantSupportRank.not_invariant component context.even context.universal context.quasisimple
    hcard context.control actor context.outside rank context.positive firstCommon secondCommon context.original context.opposite
      first second third hfirst context.second_mem context.third_mem member context.product
        context.involution context.not_common hnormalizes unused.val unused.property
          (by rw [hunusedBack]; exact fun hsupport => hnotPair (hsupportPair hsupport))
  push Not at hnotInvariant
  obtain ⟨mover, hmover, hmovesImage⟩ := hnotInvariant
  let moving : ↥(first ⊓ UniversalOrbitBlock.normalizer opposite) := ⟨mover, hmover⟩
  have htransport (mover : ↥(first ⊓ UniversalOrbitBlock.normalizer opposite)) :
      BlockSupport.support opposite ((MulAut.conj mover.val) member.val) =
        (fun factor => UniversalOrbitBlock.conjugate factor mover.val) '' support :=
    BlockSupport.support_conjugate opposite hevenOpposite huniversalOpposite hquasisimpleOpposite mover.val mover.property.2 member.val
  have hmoves : BlockSupport.support opposite ((MulAut.conj moving.val) member.val) ≠ support := by
    rw [htransport]
    exact hmovesImage
  have hcover (mover : ↥(first ⊓ UniversalOrbitBlock.normalizer opposite))
      (hmoves : BlockSupport.support opposite ((MulAut.conj mover.val) member.val) ≠ support) :
      support ∪ BlockSupport.support opposite ((MulAut.conj mover.val) member.val) = UniversalOrbitBlock.block opposite :=
    BlockSupportDisplacement.moves_cover component context.even context.universal context.quasisimple hcard first hfirst
      actor context.outside member (context.involution ▸ pow_orderOf_eq_one member.val) hnormalizes mover hmoves
  have hsize (mover : ↥(first ⊓ UniversalOrbitBlock.normalizer opposite)) :
      (BlockSupport.support opposite ((MulAut.conj mover.val) member.val)).ncard = support.ncard := by
    rw [htransport]
    exact Set.ncard_image_of_injective support (Subgroup.map_injective (MulAut.conj mover.val).injective)
  obtain ⟨hsupport, hmoving⟩ := FiniteSupportGeometry.cover_pair (UniversalOrbitBlock.block opposite) pair support
    (BlockSupport.support opposite ((MulAut.conj moving.val) member.val)) hambient hpair hsupportPair
      (BlockSupport.support_le _ _) (hsize moving) (hcover moving hmoves)
  refine ⟨hsupport, ?_, moving, hmoving⟩
  intro mover
  by_cases heq : BlockSupport.support opposite ((MulAut.conj mover.val) member.val) = support
  · exact Or.inl (heq.trans hsupport)
  · exact Or.inr (FiniteSupportGeometry.cover_pair (UniversalOrbitBlock.block opposite) pair support
      (BlockSupport.support opposite ((MulAut.conj mover.val) member.val)) hambient hpair hsupportPair
        (BlockSupport.support_le _ _) (hsize mover) (hcover mover heq)).2

end CFSG.ComponentClassification.BlockFourFactorSupport
