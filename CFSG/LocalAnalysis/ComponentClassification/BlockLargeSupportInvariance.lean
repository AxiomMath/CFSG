module

public import CFSG.LocalAnalysis.ComponentClassification.BlockSupportDisplacement
public import CFSG.LocalAnalysis.ComponentClassification.FiniteSupportGeometry

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockLargeSupportInvariance

theorem unchanged_of_unused {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (member : UniversalOrbitBlock.generated (UniversalOrbitBlock.conjugate component actor))
    (exponent : ℕ) (hpower : member.val ^ (2 ^ exponent) = 1)
    (hnormalizes : member.val ∈ Subgroup.normalizer (first : Set G))
    (mover : ↥(first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor)))
    (unused : Subgroup G) (hunused : unused ∈ UniversalOrbitBlock.block component)
    (hnot : UniversalOrbitBlock.conjugate unused actor ∉
      BlockSupport.support (UniversalOrbitBlock.conjugate component actor) member.val ∪
        BlockSupport.support (UniversalOrbitBlock.conjugate component actor) ((MulAut.conj mover.val) member.val)) :
    BlockSupport.support (UniversalOrbitBlock.conjugate component actor) ((MulAut.conj mover.val) member.val) =
      BlockSupport.support (UniversalOrbitBlock.conjugate component actor) member.val := by
  let opposite := UniversalOrbitBlock.conjugate component actor
  have horbit := UniversalOrbitBlock.orbit_conjugate component component (UniversalOrbitBlock.mem_orbit_self component) actor
  have hevenOpposite := UniversalOrbitBlock.orbit_even component heven _ horbit
  have huniversalOpposite := UniversalOrbitBlock.orbit_universal component huniversal _ horbit
  let moved : UniversalOrbitBlock.generated opposite := ⟨(MulAut.conj mover.val) member.val,
    (Subgroup.mem_normalizer_iff.mp mover.property.2 member.val).mp member.property⟩
  let subset := BlockSupport.support opposite member.val ∪ BlockSupport.support opposite moved.val
  have hsubset : subset ⊆ UniversalOrbitBlock.block opposite :=
    Set.union_subset (BlockSupport.support_le opposite member.val) (BlockSupport.support_le opposite moved.val)
  have hdisplacementSupport : BlockSupport.support opposite (member.val⁻¹ * moved.val) ⊆ subset := by
    have hsupport := BlockSupport.support_mul opposite member.val⁻¹ moved.val
    rw [BlockSupport.support_inv] at hsupport
    exact hsupport
  have hdisplacementSubset : member.val⁻¹ * moved.val ∈ BlockProperSupportOdd.subgroup opposite subset :=
    (BlockSupport.support_subproduct opposite hevenOpposite huniversalOpposite subset hsubset (member⁻¹ * moved)).mp
      hdisplacementSupport
  have hdisplacementFirst : member.val⁻¹ * moved.val ∈ first :=
    BlockSupportDisplacement.displacement_mem first member.val mover.val hnormalizes mover.property.1
  have hodd := BlockProperSupportOdd.odd component heven huniversal hquasisimple hcard
    first hfirst actor hactor subset hsubset unused hunused hnot
  have hoddOrder : Odd (orderOf (member.val⁻¹ * moved.val)) := hodd.of_dvd_nat
    ((first ⊓ BlockProperSupportOdd.subgroup opposite subset).orderOf_dvd_natCard ⟨hdisplacementFirst, hdisplacementSubset⟩)
  have hmovedPower : moved.val ^ (2 ^ exponent) = 1 := by
    change ((MulAut.conj mover.val) member.val) ^ (2 ^ exponent) = 1
    rw [← map_pow, hpower, map_one]
  exact (BlockSupport.support_eq_of_odd_two_displacement opposite hevenOpposite huniversalOpposite
    member moved exponent exponent hpower hmovedPower hoddOrder).symm

theorem invariant {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 5 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : second ≠ third)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (member : UniversalOrbitBlock.generated (UniversalOrbitBlock.conjugate component actor))
    (exponent : ℕ) (hpower : member.val ^ (2 ^ exponent) = 1)
    (hmember : member.val ∈ UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor)
    (hnormalizes : member.val ∈ Subgroup.normalizer (first : Set G))
    (mover : ↥(first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor))) :
    BlockSupport.support (UniversalOrbitBlock.conjugate component actor) ((MulAut.conj mover.val) member.val) =
      BlockSupport.support (UniversalOrbitBlock.conjugate component actor) member.val := by
  let opposite := UniversalOrbitBlock.conjugate component actor
  let support := BlockSupport.support opposite member.val
  let moved := BlockSupport.support opposite ((MulAut.conj mover.val) member.val)
  have horbit := UniversalOrbitBlock.orbit_conjugate component component (UniversalOrbitBlock.mem_orbit_self component) actor
  have hevenOpposite := UniversalOrbitBlock.orbit_even component heven _ horbit
  have huniversalOpposite := UniversalOrbitBlock.orbit_universal component huniversal _ horbit
  have hquasisimpleOpposite := UniversalOrbitBlock.orbit_quasisimple component hquasisimple _ horbit
  have hsupportPair := BlockSupport.support_pair opposite hevenOpposite huniversalOpposite
    (UniversalOrbitBlock.conjugate second actor) (UniversalOrbitBlock.conjugate third actor)
      ((OrbitBlockConjugation.block component second actor).mpr hsecond)
      ((OrbitBlockConjugation.block component third actor).mpr hthird) member hmember
  have hpair : ({UniversalOrbitBlock.conjugate second actor, UniversalOrbitBlock.conjugate third actor} : Set (Subgroup G)).ncard = 2 :=
    Set.ncard_pair (fun heq => hdistinct (Subgroup.map_injective (MulAut.conj actor).injective heq))
  have hsupportSize : support.ncard ≤ 2 := (Set.ncard_le_ncard hsupportPair).trans_eq hpair
  have htransport : moved = (fun factor => UniversalOrbitBlock.conjugate factor mover.val) '' support :=
    BlockSupport.support_conjugate opposite hevenOpposite huniversalOpposite hquasisimpleOpposite mover.val mover.property.2 member.val
  have hmovedSize : moved.ncard = support.ncard := by
    rw [htransport]
    exact Set.ncard_image_of_injective support (Subgroup.map_injective (MulAut.conj mover.val).injective)
  have hsum := Set.ncard_union_le support moved
  rw [hmovedSize] at hsum
  have hambient : 5 ≤ (UniversalOrbitBlock.block opposite).ncard := by
    rw [FiniteSupportGeometry.ncard_eq, ← Nat.card_congr (OrbitBlockConjugation.equivalence component actor)]
    exact hcard
  have hnotSubset : ¬ UniversalOrbitBlock.block opposite ⊆ support ∪ moved := by
    intro hsubset
    have hle := Set.ncard_le_ncard hsubset
    omega
  obtain ⟨unusedImage, hunusedImage, hnot⟩ := Set.not_subset.mp hnotSubset
  let unused := (OrbitBlockConjugation.equivalence component actor).symm ⟨unusedImage, hunusedImage⟩
  have hback : UniversalOrbitBlock.conjugate unused.val actor = unusedImage :=
    congrArg Subtype.val ((OrbitBlockConjugation.equivalence component actor).apply_symm_apply ⟨unusedImage, hunusedImage⟩)
  exact unchanged_of_unused component heven huniversal hquasisimple (by omega) first hfirst actor hactor
    member exponent hpower hnormalizes mover unused.val unused.property (by rwa [hback])

end CFSG.ComponentClassification.BlockLargeSupportInvariance
