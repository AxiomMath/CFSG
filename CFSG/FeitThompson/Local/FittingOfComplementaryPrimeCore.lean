module

public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Local.FittingMonoNormal
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p : ℕ} {X : Type*} [Group X] [Finite X]

theorem pComplCore_normal (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (pComplCore p X).Normal := Subgroup.normal_of_characteristic _

theorem notMem_primeFactors_natCard_pComplCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    p ∉ (Nat.card (pComplCore p X)).primeFactors := by
  rw [pComplCore_eq_piCore]
  exact fun hmem => (isPiSubgroup_iff.1 (isPiSubgroup_piCore _ X) p hmem).2 rfl

theorem pComplCore_subgroupOf_le_pComplCore (p : ℕ) (X : Type*) [Group X] [Finite X]
    (H : Subgroup X) : (pComplCore p X).subgroupOf H ≤ pComplCore p H := by
  refine le_pComplCore ((pComplCore_normal p X).subgroupOf H) fun hmem => ?_
  have hcard : Nat.card ((pComplCore p X).subgroupOf H)
      = Nat.card (pComplCore p X ⊓ H : Subgroup X) := by
    rw [← Subgroup.subgroupOf_map_subtype]
    exact (Subgroup.card_map_of_injective H.subtype_injective).symm
  rw [hcard] at hmem
  exact notMem_primeFactors_natCard_pComplCore p X
    (Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_left) Nat.card_pos.ne' hmem)

theorem map_subtype_pComplCore_fittingRaw (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (pComplCore p (fittingRaw X)).map (fittingRaw X).subtype
      = fittingRaw X ⊓ pComplCore p X := by
  have hFn : (fittingRaw X).Normal := fittingRaw_normal X
  refine le_antisymm (le_inf (Subgroup.map_subtype_le _) ?_) ?_
  · refine le_pComplCore ConjAct.normal_of_characteristic_of_normal ?_
    rw [Subgroup.card_map_of_injective (fittingRaw X).subtype_injective]
    exact notMem_primeFactors_natCard_pComplCore p (fittingRaw X)
  · calc fittingRaw X ⊓ pComplCore p X
        = ((pComplCore p X).subgroupOf (fittingRaw X)).map (fittingRaw X).subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_comm]
      _ ≤ _ := Subgroup.map_mono (pComplCore_subgroupOf_le_pComplCore p X _)

theorem map_subtype_fittingRaw_pComplCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (fittingRaw (pComplCore p X)).map (pComplCore p X).subtype
      = fittingRaw X ⊓ pComplCore p X :=
  map_subtype_fittingRaw_eq_inf (pComplCore_normal p X)

theorem map_subtype_fittingRaw_pComplCore_eq_map_subtype_pComplCore_fittingRaw
    (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (fittingRaw (pComplCore p X)).map (pComplCore p X).subtype
      = (pComplCore p (fittingRaw X)).map (fittingRaw X).subtype := by
  rw [map_subtype_fittingRaw_pComplCore, map_subtype_pComplCore_fittingRaw]

theorem fittingRaw_pComplCore_eq_subgroupOf (p : ℕ) (X : Type*) [Group X] [Finite X] :
    fittingRaw (pComplCore p X)
      = ((pComplCore p (fittingRaw X)).map (fittingRaw X).subtype).subgroupOf
          (pComplCore p X) := by
  rw [← Subgroup.map_subtype_inj, Subgroup.subgroupOf_map_subtype,
    map_subtype_fittingRaw_pComplCore, map_subtype_pComplCore_fittingRaw, inf_assoc, inf_idem]

theorem pComplCore_fittingRaw_eq_subgroupOf (p : ℕ) (X : Type*) [Group X] [Finite X] :
    pComplCore p (fittingRaw X)
      = ((fittingRaw (pComplCore p X)).map (pComplCore p X).subtype).subgroupOf
          (fittingRaw X) := by
  rw [← Subgroup.map_subtype_inj, Subgroup.subgroupOf_map_subtype,
    map_subtype_fittingRaw_pComplCore, map_subtype_pComplCore_fittingRaw, inf_right_comm, inf_idem]

theorem natCard_fittingRaw_pComplCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    Nat.card (fittingRaw (pComplCore p X)) = Nat.card (pComplCore p (fittingRaw X)) := by
  rw [← Subgroup.card_map_of_injective (K := fittingRaw (pComplCore p X))
        (pComplCore p X).subtype_injective,
    ← Subgroup.card_map_of_injective (K := pComplCore p (fittingRaw X))
        (fittingRaw X).subtype_injective,
    map_subtype_fittingRaw_pComplCore_eq_map_subtype_pComplCore_fittingRaw]

theorem normal_map_subtype_fittingRaw_pComplCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    ((fittingRaw (pComplCore p X)).map (pComplCore p X).subtype).Normal := by
  rw [map_subtype_fittingRaw_pComplCore]
  have h1 := fittingRaw_normal X
  have h2 := pComplCore_normal p X
  exact Subgroup.normal_inf_normal _ _

end

end CFSG.FeitThompson
