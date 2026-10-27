module

public import CFSG.GroupTheory.CharacteristicNormalizer
public import TauCeti.Algebra.Group.NormalizerQuotient.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.GroupTheory

open Subgroup TauCeti.Subgroup

variable {G : Type*} [Group G]

abbrev normalizerQuotientImage (H C : Subgroup G) : Subgroup (normalizerQuotient C) :=
  (H.subgroupOf (normalizer (C : Set G))).map (normalizerQuotientMk C)

variable {B C : Subgroup G}

theorem le_normalizer_of_characteristic (hCB : C ≤ B) (hC : (C.subgroupOf B).Characteristic) :
    B ≤ normalizer (C : Set G) :=
  le_normalizer.trans (normalizer_le_normalizer_of_characteristic hCB hC)

variable (hCB : C ≤ B) (hC : (C.subgroupOf B).Characteristic)
include hCB hC

@[expose] def toNormalizerQuotientImage :
    normalizer (B : Set G) →*
      normalizer (normalizerQuotientImage B C : Set (normalizerQuotient C)) :=
  ((normalizerQuotientMk C).comp
      (inclusion (normalizer_le_normalizer_of_characteristic hCB hC))).codRestrict _ fun g =>
    le_normalizer_map _ (mem_map_of_mem _ (by
      rw [← subgroupOf_normalizer_eq (le_normalizer_of_characteristic hCB hC)]
      exact mem_subgroupOf.mpr g.2))

@[simp]
theorem toNormalizerQuotientImage_apply_coe (g : normalizer (B : Set G)) :
    ((toNormalizerQuotientImage hCB hC g :
        normalizer (normalizerQuotientImage B C : Set (normalizerQuotient C))) :
      normalizerQuotient C) =
      normalizerQuotientMk C ⟨g, normalizer_le_normalizer_of_characteristic hCB hC g.2⟩ :=
  rfl

end CFSG.GroupTheory

end
