module

public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockSupport

public section

open CFSG.Open

namespace CFSG.ComponentClassification.LabeledBlockPermutation

@[expose] noncomputable def permutation {G Index : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (label : Index ≃ ↥(UniversalOrbitBlock.block component)) :
    UniversalOrbitBlock.normalizer component →* Equiv.Perm Index :=
  let := BlockPermutationAction.action component heven huniversal hquasisimple
  label.symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom (UniversalOrbitBlock.normalizer component) ↥(UniversalOrbitBlock.block component))

theorem apply_label {G Index : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (label : Index ≃ ↥(UniversalOrbitBlock.block component))
    (actor : UniversalOrbitBlock.normalizer component) (point : Index) :
    (label (permutation component heven huniversal hquasisimple label actor point)).val =
      UniversalOrbitBlock.conjugate (label point).val actor.val := by
  change (label (label.symm _)).val = _
  rw [label.apply_symm_apply]
  simp only [Equiv.trans_apply, Equiv.symm_symm]
  rfl

theorem support_label {G Index : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (label : Index ≃ ↥(UniversalOrbitBlock.block component))
    (actor : UniversalOrbitBlock.normalizer component) (member : G) (point : Index) :
    (label (permutation component heven huniversal hquasisimple label actor point)).val ∈
      BlockSupport.support component ((MulAut.conj actor.val) member) ↔
        (label point).val ∈ BlockSupport.support component member := by
  rw [apply_label]
  have hmem : UniversalOrbitBlock.conjugate (label point).val actor.val ∈ UniversalOrbitBlock.block component :=
    (UniversalOrbitBlock.normalizer_iff_preserves_block component heven huniversal hquasisimple actor.val).mp
      actor.property (label point).val (label point).property
  change (UniversalOrbitBlock.conjugate (label point).val actor.val ∈ UniversalOrbitBlock.block component ∧ _) ↔
    ((label point).val ∈ UniversalOrbitBlock.block component ∧ _)
  rw [and_iff_right hmem, and_iff_right (label point).property]
  exact not_congr (CommutingFamilySupport.centralizer_transport (MulAut.conj actor.val) (label point).val member)

@[expose] noncomputable def image {G Index : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (label : Index ≃ ↥(UniversalOrbitBlock.block component)) (factor : Subgroup G) : Subgroup (Equiv.Perm Index) :=
  (factor.subgroupOf (UniversalOrbitBlock.normalizer component)).map
    (permutation component heven huniversal hquasisimple label)

theorem image_commutes {G Index : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (label : Index ≃ ↥(UniversalOrbitBlock.block component))
    (first second : Subgroup G) (hcommutes : ⁅first, second⁆ = ⊥) :
    ⁅image component heven huniversal hquasisimple label first,
      image component heven huniversal hquasisimple label second⁆ = ⊥ := by
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  rintro left ⟨firstActor, hfirstActor, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  rintro right ⟨secondActor, hsecondActor, rfl⟩
  rw [← map_mul, ← map_mul]
  apply congrArg (permutation component heven huniversal hquasisimple label)
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes hfirstActor) secondActor.val hsecondActor

end CFSG.ComponentClassification.LabeledBlockPermutation
