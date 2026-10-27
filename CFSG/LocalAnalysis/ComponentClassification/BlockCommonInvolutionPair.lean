module

public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.BlockCommonInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.BlockCommonCentralizers

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockCommonInvolutionPair

theorem image_centralizes {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (actor : G) (elementary : Subgroup G)
    (hcontained : ∀ factor ∈ UniversalOrbitBlock.block component,
      elementary ≤ UniversalOrbitBlock.conjugate factor actor) :
    ∀ factor ∈ UniversalOrbitBlock.block component,
      elementary ≤ Subgroup.centralizer (UniversalOrbitBlock.conjugate factor actor : Set G) := by
  have horbit := UniversalOrbitBlock.orbit_conjugate component component
    (UniversalOrbitBlock.mem_orbit_self component) actor
  have hconjugateEven := UniversalOrbitBlock.orbit_even component heven _ horbit
  have hconjugateUniversal := UniversalOrbitBlock.orbit_universal component huniversal _ horbit
  have hconjugateCard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block (UniversalOrbitBlock.conjugate component actor)) := by
    rw [← Nat.card_congr (OrbitBlockConjugation.equivalence component actor)]
    exact hcard
  have hconjugateContained : ∀ factor ∈ UniversalOrbitBlock.block (UniversalOrbitBlock.conjugate component actor),
      elementary ≤ factor := by
    intro factor hfactor
    have hback := (OrbitBlockConjugation.block (UniversalOrbitBlock.conjugate component actor) factor actor⁻¹).mpr hfactor
    rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one] at hback
    have hle := hcontained (UniversalOrbitBlock.conjugate factor actor⁻¹) hback
    rwa [UniversalOrbitBlock.conjugate_conjugate, mul_inv_cancel, UniversalOrbitBlock.conjugate_one] at hle
  intro factor hfactor
  exact BlockCommonInvolutionStructure.centralizes_factors _ hconjugateEven hconjugateUniversal hconjugateCard
    elementary hconjugateContained _ ((OrbitBlockConjugation.block component factor actor).mpr hfactor)

theorem image_normalizes {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (actor : G) (elementary : Subgroup G) (helementary : IsElemAbelian 2 elementary)
    (hcontained : ∀ factor ∈ UniversalOrbitBlock.block component,
      elementary ≤ UniversalOrbitBlock.conjugate factor actor ⊓ UniversalOrbitBlock.normalizer component)
    (hcharacterization : ∀ factor ∈ UniversalOrbitBlock.block component, ∀ member : G,
      member ∈ UniversalOrbitBlock.conjugate factor actor ⊓ UniversalOrbitBlock.normalizer component ∧
        orderOf member = 2 ↔ member ∈ elementary ∧ member ≠ 1) :
    UniversalOrbitBlock.normalizer component ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom ≤
        Subgroup.normalizer (elementary : Set G) := by
  have horbit := UniversalOrbitBlock.orbit_conjugate component component
    (UniversalOrbitBlock.mem_orbit_self component) actor
  have hconjugateEven := UniversalOrbitBlock.orbit_even component heven _ horbit
  have hconjugateUniversal := UniversalOrbitBlock.orbit_universal component huniversal _ horbit
  have hconjugateQuasisimple := UniversalOrbitBlock.orbit_quasisimple component hquasisimple _ horbit
  have hback := OrbitBlockConjugation.normalizer_back component actor
  have hconjugateContained : ∀ factor ∈ UniversalOrbitBlock.block (UniversalOrbitBlock.conjugate component actor),
      elementary ≤ factor ⊓ (UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor)).map
        (MulAut.conj actor⁻¹).toMonoidHom := by
    intro factor hfactor
    have hfactorBack := (OrbitBlockConjugation.block (UniversalOrbitBlock.conjugate component actor) factor actor⁻¹).mpr hfactor
    rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one] at hfactorBack
    have hle := hcontained (UniversalOrbitBlock.conjugate factor actor⁻¹) hfactorBack
    rw [UniversalOrbitBlock.conjugate_conjugate, mul_inv_cancel, UniversalOrbitBlock.conjugate_one] at hle
    rwa [hback]
  have hconjugateCharacterization : ∀ factor ∈ UniversalOrbitBlock.block (UniversalOrbitBlock.conjugate component actor),
      ∀ member : G, member ∈ factor ⊓ (UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor)).map
        (MulAut.conj actor⁻¹).toMonoidHom ∧ orderOf member = 2 ↔ member ∈ elementary ∧ member ≠ 1 := by
    intro factor hfactor member
    have hfactorBack := (OrbitBlockConjugation.block (UniversalOrbitBlock.conjugate component actor) factor actor⁻¹).mpr hfactor
    rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one] at hfactorBack
    have hiff := hcharacterization (UniversalOrbitBlock.conjugate factor actor⁻¹) hfactorBack member
    rw [UniversalOrbitBlock.conjugate_conjugate, mul_inv_cancel, UniversalOrbitBlock.conjugate_one] at hiff
    rwa [hback]
  have hnormal := BlockCommonInvolutionStructure.normalizes_common _ hconjugateEven hconjugateUniversal
    hconjugateQuasisimple actor⁻¹ elementary helementary hconjugateContained hconjugateCharacterization
  rw [hback, ← OrbitBlockConjugation.normalizer component actor, inf_comm] at hnormal
  exact hnormal

theorem normalized_disjoint_commute {G : Type*} [Group G]
    (overgroup first second : Subgroup G) (hfirst : first ≤ overgroup) (hsecond : second ≤ overgroup)
    (hnormalFirst : overgroup ≤ Subgroup.normalizer (first : Set G))
    (hnormalSecond : overgroup ≤ Subgroup.normalizer (second : Set G)) (hdisjoint : Disjoint first second) :
    ⁅first, second⁆ = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← disjoint_iff.mp hdisjoint]
  apply Subgroup.commutator_le.mpr
  intro firstMember hfirstMember secondMember hsecondMember
  rw [commutatorElement_def]
  constructor
  · have hconjugate := (Subgroup.mem_normalizer_iff.mp (hnormalFirst (hsecond hsecondMember)) firstMember⁻¹).mp
      (first.inv_mem hfirstMember)
    change firstMember * secondMember * firstMember⁻¹ * secondMember⁻¹ ∈ first
    simpa only [mul_assoc] using first.mul_mem hfirstMember hconjugate
  · exact second.mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hnormalSecond (hfirst hfirstMember)) secondMember).mp hsecondMember)
      (second.inv_mem hsecondMember)

theorem centralizer_eq {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (actor : G) (elementary : Subgroup G) (helementary : IsElemAbelian 2 elementary)
    (hnontrivial : Nontrivial elementary)
    (hcontained : ∀ factor ∈ UniversalOrbitBlock.block component, elementary ≤ UniversalOrbitBlock.conjugate factor actor)
    (first : Subgroup G)
    (hcentralizes : first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom ≤
      Subgroup.centralizer (elementary : Set G)) :
    first ⊓ Subgroup.centralizer (elementary : Set G) =
      first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom := by
  obtain ⟨member, hmember, hne⟩ := (elementary.nontrivial_iff_exists_ne_one).mp hnontrivial
  apply le_antisymm
  · intro central hcentral
    have hsingleton : central ∈ first ⊓ Subgroup.centralizer {member} :=
      ⟨hcentral.1, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hcentral.2 member hmember).symm⟩
    rw [BlockCommonCentralizers.singleton_eq component heven huniversal hquasisimple hcard elementary helementary
      actor hcontained first hcentralizes member hmember hne] at hsingleton
    exact hsingleton
  · exact le_inf inf_le_left hcentralizes

end CFSG.ComponentClassification.BlockCommonInvolutionPair
