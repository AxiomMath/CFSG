module

public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ComponentClassification.EvenQuasisimpleOddCore

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockProperTwoAction

theorem core_join_ne {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component) :
    (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) ⊔
      (componentClassificationOddCore first).map first.subtype ≠ first := by
  let imageNormalizer := (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom
  let intersection := imageNormalizer.subgroupOf first
  have hcore : componentClassificationOddCore first ≤ Subgroup.center first :=
    EvenQuasisimpleOddCore.le_center (UniversalOrbitBlock.orbit_quasisimple component hquasisimple first hfirst.1)
      (UniversalOrbitBlock.orbit_even component heven first hfirst.1)
  have hproper := BlockMutualAction.intersection_center_join_ne_top component heven huniversal hquasisimple hcard
    hcontrol first hfirst actor hactor
  have hintersectionMap : intersection.map first.subtype = first ⊓ imageNormalizer := by
    ext member
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      exact ⟨lift.property, hlift⟩
    · intro hmember
      exact Subgroup.mem_map.mpr ⟨⟨member, hmember.1⟩, hmember.2, rfl⟩
  intro hcover
  have hlocalCover : intersection ⊔ componentClassificationOddCore first = ⊤ := by
    apply Subgroup.map_injective first.subtype_injective
    rw [Subgroup.map_sup, hintersectionMap]
    rw [hcover, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply hproper
  apply top_unique
  rw [← hlocalCover]
  exact sup_le le_sup_left (hcore.trans le_sup_right)

theorem abelian_embedding {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : second ≠ third)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (firstTwo secondTwo : Subgroup G)
    (hfirstTwo : IsPGroup 2 firstTwo) (hsecondTwo : IsPGroup 2 secondTwo)
    (hne : firstTwo ≠ ⊥)
    (hfirstContained : firstTwo ≤ UniversalOrbitBlock.conjugate second actor)
    (hsecondContained : secondTwo ≤ UniversalOrbitBlock.conjugate third actor)
    (hfirstNormalizes : firstTwo ≤ Subgroup.normalizer (first : Set G))
    (hsecondNormalizes : secondTwo ≤ Subgroup.normalizer (first : Set G)) :
    IsMulCommutative ↥(firstTwo ⊔ secondTwo) ∧
      ∃ homomorphism : ↥(firstTwo ⊔ secondTwo) →*
          ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom),
        Function.Injective homomorphism := by
  obtain ⟨hnormalizes, htwo, _, hintersectionNormalizes, hdisjoint, _, hcentralizers, hcommutator, _⟩ :=
    BlockTwoProductAction.action component heven huniversal hquasisimple hcard hcontrol first second third
      hfirst hsecond hthird hdistinct actor hactor firstTwo secondTwo hfirstTwo hsecondTwo hne
        hfirstContained hsecondContained hfirstNormalizes hsecondNormalizes
  exact TwoActionProperEmbedding.embedding first (firstTwo ⊔ secondTwo)
    (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)
    inf_le_left htwo hdisjoint hnormalizes hintersectionNormalizes hcentralizers hcommutator
    (core_join_ne component heven huniversal hquasisimple hcard hcontrol first hfirst actor hactor)

end CFSG.ComponentClassification.BlockProperTwoAction
