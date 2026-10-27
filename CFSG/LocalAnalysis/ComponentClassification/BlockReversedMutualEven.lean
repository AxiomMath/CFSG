module

public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation

public section

namespace CFSG.ComponentClassification.BlockReversedMutualEven

theorem even {G : Type*} [Group G] (component : Subgroup G) (actor : G)
    (hmutual : ∀ first ∈ UniversalOrbitBlock.block component, ∀ second ∈ UniversalOrbitBlock.block component,
      Even (Nat.card ↥(first ⊓ Subgroup.normalizer (UniversalOrbitBlock.conjugate second actor : Set G))) ∧
        Even (Nat.card ↥(UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G)))) :
    ∀ first ∈ UniversalOrbitBlock.block (UniversalOrbitBlock.conjugate component actor),
      ∀ second ∈ UniversalOrbitBlock.block (UniversalOrbitBlock.conjugate component actor),
        Even (Nat.card ↥(first ⊓ Subgroup.normalizer (UniversalOrbitBlock.conjugate second actor⁻¹ : Set G))) ∧
          Even (Nat.card ↥(UniversalOrbitBlock.conjugate second actor⁻¹ ⊓ Subgroup.normalizer (first : Set G))) := by
  intro first hfirst second hsecond
  let originalFirst := UniversalOrbitBlock.conjugate first actor⁻¹
  let originalSecond := UniversalOrbitBlock.conjugate second actor⁻¹
  have hfirstOriginal : originalFirst ∈ UniversalOrbitBlock.block component := by
    have hmem := (OrbitBlockConjugation.block (UniversalOrbitBlock.conjugate component actor) first actor⁻¹).mpr hfirst
    rwa [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one] at hmem
  have hsecondOriginal : originalSecond ∈ UniversalOrbitBlock.block component := by
    have hmem := (OrbitBlockConjugation.block (UniversalOrbitBlock.conjugate component actor) second actor⁻¹).mpr hsecond
    rwa [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one] at hmem
  have hrestore : UniversalOrbitBlock.conjugate originalFirst actor = first := by
    change UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate first actor⁻¹) actor = first
    rw [UniversalOrbitBlock.conjugate_conjugate, mul_inv_cancel, UniversalOrbitBlock.conjugate_one]
  have heven := hmutual originalSecond hsecondOriginal originalFirst hfirstOriginal
  rw [hrestore] at heven
  exact ⟨heven.2, heven.1⟩

end CFSG.ComponentClassification.BlockReversedMutualEven
