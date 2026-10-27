module

public import CFSG.LocalAnalysis.ComponentClassification.BlockSupport

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockSupportDisplacement

theorem displacement_mem {G : Type*} [Group G] (ambient : Subgroup G)
    (member mover : G) (hmember : member ∈ Subgroup.normalizer (ambient : Set G))
    (hmover : mover ∈ ambient) : member⁻¹ * (MulAut.conj mover) member ∈ ambient := by
  have hconjugate : member⁻¹ * mover * member ∈ ambient :=
    (Subgroup.mem_normalizer_iff''.mp hmember mover).mp hmover
  convert ambient.mul_mem hconjugate (ambient.inv_mem hmover) using 1
  simp only [MulAut.conj_apply]
  group

theorem unchanged_of_unused {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (member : UniversalOrbitBlock.generated (UniversalOrbitBlock.conjugate component actor))
    (hsquare : member.val ^ 2 = 1) (hnormalizes : member.val ∈ Subgroup.normalizer (first : Set G))
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
    displacement_mem first member.val mover.val hnormalizes mover.property.1
  have hodd := BlockProperSupportOdd.odd component heven huniversal hquasisimple hcard
    first hfirst actor hactor subset hsubset unused hunused hnot
  have hoddOrder : Odd (orderOf (member.val⁻¹ * moved.val)) := hodd.of_dvd_nat
    ((first ⊓ BlockProperSupportOdd.subgroup opposite subset).orderOf_dvd_natCard
      ⟨hdisplacementFirst, hdisplacementSubset⟩)
  have hmovedSquare : moved.val ^ 2 = 1 := by
    change ((MulAut.conj mover.val) member.val) ^ 2 = 1
    rw [← map_pow, hsquare, map_one]
  exact (BlockSupport.support_eq_of_odd_displacement opposite hevenOpposite huniversalOpposite
    member moved hsquare hmovedSquare hoddOrder).symm

theorem moves_cover {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (member : UniversalOrbitBlock.generated (UniversalOrbitBlock.conjugate component actor))
    (hsquare : member.val ^ 2 = 1) (hnormalizes : member.val ∈ Subgroup.normalizer (first : Set G))
    (mover : ↥(first ⊓ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor)))
    (hmoves : BlockSupport.support (UniversalOrbitBlock.conjugate component actor) ((MulAut.conj mover.val) member.val) ≠
      BlockSupport.support (UniversalOrbitBlock.conjugate component actor) member.val) :
    BlockSupport.support (UniversalOrbitBlock.conjugate component actor) member.val ∪
      BlockSupport.support (UniversalOrbitBlock.conjugate component actor) ((MulAut.conj mover.val) member.val) =
        UniversalOrbitBlock.block (UniversalOrbitBlock.conjugate component actor) := by
  apply Set.Subset.antisymm
  · exact Set.union_subset (BlockSupport.support_le _ _) (BlockSupport.support_le _ _)
  · intro factor hfactor
    by_contra hnot
    let original := (OrbitBlockConjugation.equivalence component actor).symm ⟨factor, hfactor⟩
    have hback : UniversalOrbitBlock.conjugate original.val actor = factor :=
      congrArg Subtype.val ((OrbitBlockConjugation.equivalence component actor).apply_symm_apply ⟨factor, hfactor⟩)
    exact hmoves (unchanged_of_unused component heven huniversal hquasisimple hcard first hfirst actor hactor
      member hsquare hnormalizes mover original.val original.property (by rwa [hback]))

end CFSG.ComponentClassification.BlockSupportDisplacement
