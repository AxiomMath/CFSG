module

public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentClassification.ConjugationPairStabilizer
public import CFSG.LocalAnalysis.ComponentClassification.OrbitImageTransport

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.ComponentClassification.BlockPermutationAction

@[expose, instance_reducible] noncomputable def action {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component) :
    MulAction (UniversalOrbitBlock.normalizer component) ↥(UniversalOrbitBlock.block component) where
  smul actor factor := ⟨UniversalOrbitBlock.conjugate factor.val actor.val,
    (UniversalOrbitBlock.normalizer_iff_preserves_block component heven huniversal hquasisimple actor.val).mp
      actor.property factor.val factor.property⟩
  one_smul factor := Subtype.ext (UniversalOrbitBlock.conjugate_one factor.val)
  mul_smul first second factor := Subtype.ext (UniversalOrbitBlock.conjugate_conjugate factor.val second.val first.val).symm

@[expose] noncomputable def permutation {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (label : Fin 3 ≃ ↥(UniversalOrbitBlock.block component)) :
    UniversalOrbitBlock.normalizer component →* Equiv.Perm (Fin 3) :=
  let := action component heven huniversal hquasisimple
  label.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom (UniversalOrbitBlock.normalizer component)
    ↥(UniversalOrbitBlock.block component))

theorem apply_label {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (label : Fin 3 ≃ ↥(UniversalOrbitBlock.block component))
    (actor : UniversalOrbitBlock.normalizer component) (point : Fin 3) :
    (label (permutation component heven huniversal hquasisimple label actor point)).val =
      UniversalOrbitBlock.conjugate (label point).val actor.val := by
  change (label (label.symm _)).val = _
  rw [label.apply_symm_apply]
  simp only [Equiv.trans_apply, Equiv.symm_symm]
  rfl

theorem orbit_card {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (label : Fin 3 ≃ ↥(UniversalOrbitBlock.block component))
    (acting : Subgroup G) (hnormalizes : acting ≤ UniversalOrbitBlock.normalizer component)
    (first second : Fin 3) :
    Nat.card ↥(ConjugationPairStabilizer.orbit acting (label first).val (label second).val) =
      Nat.card ↥(MulAction.orbit
        (permutation component heven huniversal hquasisimple label |>.comp (Subgroup.inclusion hnormalizes)).range
          ({first, second} : Set (Fin 3))) := by
  let := ConjugationPairStabilizer.action (G := G)
  let homomorphism := (permutation component heven huniversal hquasisimple label).comp (Subgroup.inclusion hnormalizes)
  let pointMap : Fin 3 → Subgroup G := fun point => (label point).val
  let setMap : Set (Fin 3) → Set (Subgroup G) := Set.image pointMap
  have hpointInjective : Function.Injective pointMap := by
    intro first second heq
    exact label.injective (Subtype.ext heq)
  have hinjective : Function.Injective setMap := Set.image_injective.mpr hpointInjective
  have hequivariant : ∀ actor : acting, ∀ pair : Set (Fin 3),
      actor • setMap pair = setMap (homomorphism.rangeRestrict actor • pair) := by
    intro actor pair
    ext member
    constructor
    · rintro ⟨preimage, ⟨point, hpoint, rfl⟩, rfl⟩
      refine ⟨homomorphism actor point, ?_, ?_⟩
      · exact Set.smul_mem_smul_set hpoint
      · exact apply_label component heven huniversal hquasisimple label (Subgroup.inclusion hnormalizes actor) point
    · rintro ⟨point, ⟨preimage, hpreimage, rfl⟩, rfl⟩
      refine ⟨pointMap preimage, ⟨preimage, hpreimage, rfl⟩, ?_⟩
      exact (apply_label component heven huniversal hquasisimple label (Subgroup.inclusion hnormalizes actor) preimage).symm
  have hcard := OrbitImageTransport.card homomorphism.rangeRestrict homomorphism.rangeRestrict_surjective setMap hinjective
    hequivariant ({first, second} : Set (Fin 3))
  change Nat.card ↥(MulAction.orbit homomorphism.range ({first, second} : Set (Fin 3))) =
    Nat.card ↥(MulAction.orbit acting (pointMap '' ({first, second} : Set (Fin 3)))) at hcard
  rw [Set.image_pair] at hcard
  exact hcard.symm

end CFSG.ComponentClassification.BlockPermutationAction
