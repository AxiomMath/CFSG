module

public import CFSG.LocalAnalysis.ComponentClassification.BlockCommonInvolutionPackage
public import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleStrictSylowIntersection

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockStrictSylowIntersections

theorem right_common_normalizes {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (elementary : Subgroup G) (helementary : IsElemAbelian 2 elementary)
    (hcontained : ∀ factor ∈ UniversalOrbitBlock.block component,
      elementary ≤ UniversalOrbitBlock.conjugate factor actor ⊓ UniversalOrbitBlock.normalizer component)
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component) :
    elementary ≤ Subgroup.normalizer (first : Set G) := by
  intro member hmember
  by_cases hone : member = 1
  · rw [hone]
    exact (Subgroup.normalizer _).one_mem
  · exact BlockMutualRanks.image_involution_normalizes component heven huniversal hcard hcontrol first component hfirst
      (UniversalOrbitBlock.mem_block_self component) actor hactor member
        (hcontained component (UniversalOrbitBlock.mem_block_self component) hmember)
        (orderOf_eq_prime (helementary.2 member hmember) hone)

theorem forward {G : Type*} [Group G] [Finite G]
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
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component) :
    ∀ firstSylow : Sylow 2 ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom),
      ∀ secondSylow : Sylow 2 first,
        Nat.card (firstSylow : Subgroup ↥(first ⊓
          (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) <
            Nat.card (secondSylow : Subgroup first) := by
  have hself := UniversalOrbitBlock.mem_block_self component
  have hsecondContained : ∀ factor ∈ UniversalOrbitBlock.block component,
      secondCommon ≤ UniversalOrbitBlock.conjugate factor actor ⊓ UniversalOrbitBlock.normalizer component :=
    fun factor hfactor => hsecondProperties.contained _ ((OrbitBlockConjugation.block component factor actor).mpr hfactor)
  have hsecondInvolutions : ∀ factor ∈ UniversalOrbitBlock.block component, ∀ member : G,
      member ∈ UniversalOrbitBlock.conjugate factor actor ⊓ UniversalOrbitBlock.normalizer component ∧ orderOf member = 2 ↔
        member ∈ secondCommon ∧ member ≠ 1 :=
    fun factor hfactor => hsecondProperties.involutions _ ((OrbitBlockConjugation.block component factor actor).mpr hfactor)
  have hnormalizes := right_common_normalizes component heven huniversal hcard hcontrol actor hactor secondCommon
    hsecondProperties.isElementary hsecondContained first hfirst
  have htwo := InvolutionGeneratedSubgroup.two_of_elementary secondCommon hsecondProperties.isElementary
  have hcontained : secondCommon ≤ UniversalOrbitBlock.conjugate component actor ⊔ UniversalOrbitBlock.conjugate component actor :=
    ((hsecondContained component hself).trans inf_le_left).trans le_sup_left
  have hfaithful := BlockTwoActionFaithful.action_injective component heven huniversal hquasisimple hcard
    first component component hfirst hself hself actor hactor secondCommon htwo hcontained hnormalizes
  have hdisjoint := BlockTwoActionFaithful.disjoint_factor component heven huniversal hquasisimple hcard
    first component component hfirst hself hself actor hactor secondCommon htwo hcontained
  have hsecondNormal := BlockCommonInvolutionPair.image_normalizes component heven huniversal hquasisimple actor
    secondCommon hsecondProperties.isElementary hsecondContained hsecondInvolutions
  have hcentralizes := Subgroup.le_centralizer_iff.mp
    (BlockCommonCentralizers.intersection_centralizes component heven huniversal hquasisimple hcard hcontrol actor hactor
      secondCommon hsecondProperties.isElementary hsecondContained hsecondNormal first hfirst)
  have hnotContained := QuasisimpleStrictSylowIntersection.not_contained first
    (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) firstCommon secondCommon
      (UniversalOrbitBlock.orbit_quasisimple component hquasisimple first hfirst.1)
      (UniversalOrbitBlock.orbit_even component heven first hfirst.1)
      (hfirstProperties.factor_center heven huniversal hcard first hfirst)
      (fun member hmember horder => ((hfirstProperties.involutions first hfirst member).mp ⟨hmember, horder⟩).1)
      hsecondProperties.isElementary (hsecondProperties.nontrivial hpositive) hnormalizes hdisjoint hcentralizes hfaithful
  exact QuasisimpleStrictSylowIntersection.card_lt first _ inf_le_left hnotContained

theorem reverse {G : Type*} [Group G] [Finite G]
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
    (second : Subgroup G) (hsecond : second ∈ UniversalOrbitBlock.block component) :
    ∀ firstSylow : Sylow 2 ↥(UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component),
      ∀ secondSylow : Sylow 2 (UniversalOrbitBlock.conjugate second actor),
        Nat.card (firstSylow : Subgroup ↥(UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component)) <
          Nat.card (secondSylow : Subgroup (UniversalOrbitBlock.conjugate second actor)) := by
  let conjugate := UniversalOrbitBlock.conjugate component actor
  have horbit := UniversalOrbitBlock.orbit_conjugate component component
    (UniversalOrbitBlock.mem_orbit_self component) actor
  have hevenConjugate := UniversalOrbitBlock.orbit_even component heven _ horbit
  have huniversalConjugate := UniversalOrbitBlock.orbit_universal component huniversal _ horbit
  have hquasisimpleConjugate := UniversalOrbitBlock.orbit_quasisimple component hquasisimple _ horbit
  have hcardConjugate : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block conjugate) := by
    rw [← Nat.card_congr (OrbitBlockConjugation.equivalence component actor)]
    exact hcard
  have hcontrolConjugate := BlockExternalControlConjugation.control component actor hcontrol
  have houtsideConjugate := OrbitBlockConjugation.inverse_outside component actor hactor
  have hfirstReversed : BlockCommonInvolutionPackage.Common conjugate
      ((UniversalOrbitBlock.normalizer conjugate).map (MulAut.conj actor⁻¹).toMonoidHom) rank secondCommon := by
    rw [OrbitBlockConjugation.normalizer_back]
    exact hsecondProperties
  have hsecondReversed : BlockCommonInvolutionPackage.Common (UniversalOrbitBlock.conjugate conjugate actor⁻¹)
      (UniversalOrbitBlock.normalizer conjugate) rank firstCommon := by
    change BlockCommonInvolutionPackage.Common
      (UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate component actor) actor⁻¹) _ _ _
    rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one,
      ← OrbitBlockConjugation.normalizer]
    exact hfirstProperties
  have hstrict := forward conjugate hevenConjugate huniversalConjugate hquasisimpleConjugate hcardConjugate hcontrolConjugate
    actor⁻¹ houtsideConjugate rank hpositive secondCommon firstCommon hfirstReversed hsecondReversed
      (UniversalOrbitBlock.conjugate second actor) ((OrbitBlockConjugation.block component second actor).mpr hsecond)
  rw [OrbitBlockConjugation.normalizer_back] at hstrict
  exact hstrict

end CFSG.ComponentClassification.BlockStrictSylowIntersections
