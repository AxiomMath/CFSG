module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexIntersection

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

universe u

variable {G : Type u} [Group G]

theorem translated_coset_card (H : Subgroup G) (z u : G) :
    Nat.card (translatedCosetUnitSet H z u) = Nat.card (cosetUnitSet H z u) :=
  Nat.card_image_of_injective (mul_right_injective u) (cosetUnitSet H z u)

theorem normalizer_conjugacyWithin_eq (Delta : Set G) (u : G) (hu : u ∈ Delta)
    (htrans : ∀ s ∈ Delta, ∀ t ∈ Delta,
      ∃ n : Subgroup.normalizer Delta, rightConjugateElem s (n : G) = t) :
    conjugacyWithin (Subgroup.normalizer Delta) u = Delta := by
  ext s
  constructor
  · rintro ⟨n, rfl⟩
    have hn := (Subgroup.normalizer Delta).inv_mem n.property
    simpa only [rightConjugateElem, inv_inv] using
      (show ∀ v, v ∈ Delta ↔ (n : G)⁻¹ * v * (n : G)⁻¹⁻¹ ∈ Delta from hn) u |>.mp hu
  · intro hs
    exact htrans u hu s hs

theorem translated_coset_conjugation_index (H : Subgroup G) (z u : G)
    (htrans : ∀ s ∈ translatedCosetUnitSet H z u,
      ∀ t ∈ translatedCosetUnitSet H z u,
        ∃ n : Subgroup.normalizer (translatedCosetUnitSet H z u),
          rightConjugateElem s (n : G) = t) :
    (Subgroup.centralizer ({u} : Set G)).relIndex
      (Subgroup.normalizer (translatedCosetUnitSet H z u)) = Nat.card (cosetUnitSet H z u) := by
  have humem : u ∈ translatedCosetUnitSet H z u :=
    ⟨1, Set.mem_union_left _ (Set.mem_singleton 1), mul_one u⟩
  calc
    _ = Nat.card (conjugacyWithin (Subgroup.normalizer (translatedCosetUnitSet H z u)) u) :=
      (conjugacyWithin_card_eq_centralizer_index _ _).symm
    _ = Nat.card (translatedCosetUnitSet H z u) := by
      rw [normalizer_conjugacyWithin_eq _ u humem htrans]
    _ = Nat.card (cosetUnitSet H z u) := translated_coset_card H z u

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
