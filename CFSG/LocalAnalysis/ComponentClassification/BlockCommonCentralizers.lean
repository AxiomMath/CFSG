module

public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoActionFaithful
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockCommonCentralizers

theorem intersection_centralizes {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (elementary : Subgroup G) (helementary : IsElemAbelian 2 elementary)
    (hcontained : ∀ factor ∈ UniversalOrbitBlock.block component,
      elementary ≤ UniversalOrbitBlock.conjugate factor actor ⊓ UniversalOrbitBlock.normalizer component)
    (hnormal : UniversalOrbitBlock.normalizer component ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom ≤
        Subgroup.normalizer (elementary : Set G))
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component) :
    first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom ≤
      Subgroup.centralizer (elementary : Set G) := by
  let intersection := first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom
  have htwo := InvolutionGeneratedSubgroup.two_of_elementary elementary helementary
  have helementaryNormalizes : elementary ≤ Subgroup.normalizer (first : Set G) := by
    intro member hmember
    by_cases hone : member = 1
    · rw [hone]
      exact (Subgroup.normalizer _).one_mem
    · exact BlockMutualRanks.image_involution_normalizes component heven huniversal hcard hcontrol first component hfirst
        (UniversalOrbitBlock.mem_block_self component) actor hactor member
          (hcontained component (UniversalOrbitBlock.mem_block_self component) hmember)
          (orderOf_eq_prime (helementary.2 member hmember) hone)
  have hcore := BlockMutualAction.commutator_le_core component heven huniversal hquasisimple hcard first component
    hfirst (UniversalOrbitBlock.mem_block_self component) actor hactor elementary htwo
      ((hcontained component (UniversalOrbitBlock.mem_block_self component)).trans inf_le_left) helementaryNormalizes
  have hfirstNormalizer : first ≤ UniversalOrbitBlock.normalizer component :=
    (CommutingComponentFamily.factor_le _ first hfirst).trans Subgroup.le_normalizer
  have hintersectionNormalizes : intersection ≤ Subgroup.normalizer (elementary : Set G) :=
    (inf_le_inf_right _ hfirstNormalizer).trans hnormal
  have hcommutatorLe : ⁅intersection, elementary⁆ ≤ elementary := by
    apply Subgroup.commutator_le.mpr
    intro member hmember element helement
    rw [commutatorElement_def]
    exact elementary.mul_mem ((Subgroup.mem_normalizer_iff.mp (hintersectionNormalizes hmember) element).mp helement)
      (elementary.inv_mem helement)
  have hcoreOdd : Odd (Nat.card ((componentClassificationOddCore intersection).map intersection.subtype)) := by
    rw [Subgroup.card_map_of_injective intersection.subtype_injective]
    exact OddCore.odd_card intersection
  rw [Subgroup.commutator_comm] at hcommutatorLe
  have hbot := TwoActionOddIntersection.two_in_odd_eq_bot ⁅elementary, intersection⁆
    ((componentClassificationOddCore intersection).map intersection.subtype) (htwo.to_le hcommutatorLe) hcoreOdd hcore
  exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)

theorem singleton_eq {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (elementary : Subgroup G) (helementary : IsElemAbelian 2 elementary)
    (actor : G)
    (hcontained : ∀ factor ∈ UniversalOrbitBlock.block component, elementary ≤ UniversalOrbitBlock.conjugate factor actor)
    (first : Subgroup G)
    (hcentralizes : first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom ≤
      Subgroup.centralizer (elementary : Set G))
    (member : G) (hmember : member ∈ elementary) (hne : member ≠ 1) :
    first ⊓ Subgroup.centralizer {member} =
      first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom := by
  apply le_antisymm
  · intro central hcentral
    exact ⟨hcentral.1, BlockTwoActionFaithful.centralizer_le_image_normalizer component heven huniversal hquasisimple hcard
      component component (UniversalOrbitBlock.mem_block_self component) (UniversalOrbitBlock.mem_block_self component) actor
      elementary (InvolutionGeneratedSubgroup.two_of_elementary elementary helementary)
      ((hcontained component (UniversalOrbitBlock.mem_block_self component)).trans le_sup_left)
      member hmember hne hcentral.2⟩
  · intro central hcentral
    exact ⟨hcentral.1, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hcentralizes hcentral) member hmember).symm⟩

end CFSG.ComponentClassification.BlockCommonCentralizers
