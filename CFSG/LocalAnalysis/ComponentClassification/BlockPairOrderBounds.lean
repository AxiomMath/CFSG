module

public import CFSG.LocalAnalysis.ComponentClassification.BlockPrescribedSylowEmbedding

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockPairOrderBounds

theorem center_embedding_bound {G Acting : Type*} [Group G] [Group Acting] [Finite G]
    (ambient : Subgroup G) (sylow : Sylow 2 ambient)
    (homomorphism : Acting →* Subgroup.center ((sylow : Subgroup ambient).map ambient.subtype))
    (hinjective : Function.Injective homomorphism) : Nat.card Acting ≤ Nat.card (sylow : Subgroup ambient) := by
  have hbound := (Nat.card_le_card_of_injective homomorphism hinjective).trans
    (Subgroup.card_le_card_group (Subgroup.center ((sylow : Subgroup ambient).map ambient.subtype)))
  rwa [Subgroup.card_map_of_injective ambient.subtype_injective] at hbound

theorem forward {G : Type*} [Group G] [Finite G]
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
    (hfirstTwo : IsPGroup 2 firstTwo) (hsecondTwo : IsPGroup 2 secondTwo) (hne : firstTwo ≠ ⊥)
    (hfirstContained : firstTwo ≤ UniversalOrbitBlock.conjugate second actor)
    (hsecondContained : secondTwo ≤ UniversalOrbitBlock.conjugate third actor)
    (hfirstNormalizes : firstTwo ≤ Subgroup.normalizer (first : Set G))
    (hsecondNormalizes : secondTwo ≤ Subgroup.normalizer (first : Set G))
    (hstrict : ∀ left : Sylow 2 ↥(first ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom), ∀ right : Sylow 2 first,
        Nat.card (left : Subgroup ↥(first ⊓
          (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) <
            Nat.card (right : Subgroup first))
    (prescribed : Sylow 2 ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) :
    Nat.card ↥(firstTwo ⊔ secondTwo) ≤ Nat.card (prescribed : Subgroup ↥(first ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) := by
  obtain ⟨_, homomorphism, hinjective⟩ := BlockPrescribedSylowEmbedding.product component heven huniversal hquasisimple hcard
    hcontrol first second third hfirst hsecond hthird hdistinct actor hactor firstTwo secondTwo hfirstTwo hsecondTwo hne
      hfirstContained hsecondContained hfirstNormalizes hsecondNormalizes hstrict prescribed
  exact center_embedding_bound _ prescribed homomorphism hinjective

theorem reverse {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : first ≠ second)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (firstTwo secondTwo : Subgroup G)
    (hfirstTwo : IsPGroup 2 firstTwo) (hsecondTwo : IsPGroup 2 secondTwo) (hne : firstTwo ≠ ⊥)
    (hfirstContained : firstTwo ≤ first) (hsecondContained : secondTwo ≤ second)
    (hfirstNormalizes : firstTwo ≤ Subgroup.normalizer (UniversalOrbitBlock.conjugate third actor : Set G))
    (hsecondNormalizes : secondTwo ≤ Subgroup.normalizer (UniversalOrbitBlock.conjugate third actor : Set G))
    (hstrict : ∀ left : Sylow 2 ↥(UniversalOrbitBlock.conjugate third actor ⊓ UniversalOrbitBlock.normalizer component),
      ∀ right : Sylow 2 (UniversalOrbitBlock.conjugate third actor),
        Nat.card (left : Subgroup ↥(UniversalOrbitBlock.conjugate third actor ⊓ UniversalOrbitBlock.normalizer component)) <
          Nat.card (right : Subgroup (UniversalOrbitBlock.conjugate third actor)))
    (prescribed : Sylow 2 ↥(UniversalOrbitBlock.conjugate third actor ⊓ UniversalOrbitBlock.normalizer component)) :
    Nat.card ↥(firstTwo ⊔ secondTwo) ≤ Nat.card (prescribed : Subgroup ↥(UniversalOrbitBlock.conjugate third actor ⊓
      UniversalOrbitBlock.normalizer component)) := by
  let conjugate := UniversalOrbitBlock.conjugate component actor
  have horbit := UniversalOrbitBlock.orbit_conjugate component component (UniversalOrbitBlock.mem_orbit_self component) actor
  have hevenConjugate := UniversalOrbitBlock.orbit_even component heven conjugate horbit
  have huniversalConjugate := UniversalOrbitBlock.orbit_universal component huniversal conjugate horbit
  have hquasisimpleConjugate := UniversalOrbitBlock.orbit_quasisimple component hquasisimple conjugate horbit
  have hcardConjugate : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block conjugate) := by
    rw [← Nat.card_congr (OrbitBlockConjugation.equivalence component actor)]
    exact hcard
  have hfirstConjugate := (OrbitBlockConjugation.block component first actor).mpr hfirst
  have hsecondConjugate := (OrbitBlockConjugation.block component second actor).mpr hsecond
  have hthirdConjugate := (OrbitBlockConjugation.block component third actor).mpr hthird
  have hdistinctConjugate : UniversalOrbitBlock.conjugate first actor ≠ UniversalOrbitBlock.conjugate second actor := by
    intro heq
    have hback := congrArg (fun factor => UniversalOrbitBlock.conjugate factor actor⁻¹) heq
    rw [UniversalOrbitBlock.conjugate_conjugate, UniversalOrbitBlock.conjugate_conjugate,
      inv_mul_cancel, UniversalOrbitBlock.conjugate_one, UniversalOrbitBlock.conjugate_one] at hback
    exact hdistinct hback
  have hfirstBack : UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate first actor) actor⁻¹ = first := by
    rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one]
  have hsecondBack : UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate second actor) actor⁻¹ = second := by
    rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one]
  revert prescribed
  rw [← OrbitBlockConjugation.normalizer_back component actor] at hstrict ⊢
  intro prescribed
  exact forward conjugate hevenConjugate huniversalConjugate hquasisimpleConjugate hcardConjugate
    (BlockExternalControlConjugation.control component actor hcontrol) (UniversalOrbitBlock.conjugate third actor)
      (UniversalOrbitBlock.conjugate first actor) (UniversalOrbitBlock.conjugate second actor)
        hthirdConjugate hfirstConjugate hsecondConjugate hdistinctConjugate actor⁻¹
          (OrbitBlockConjugation.inverse_outside component actor hactor) firstTwo secondTwo hfirstTwo hsecondTwo hne
            (by rw [hfirstBack]; exact hfirstContained) (by rw [hsecondBack]; exact hsecondContained)
              hfirstNormalizes hsecondNormalizes hstrict prescribed

end CFSG.ComponentClassification.BlockPairOrderBounds
