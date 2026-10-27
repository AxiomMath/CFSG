module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
import CFSG.FeitThompson.Local.NormalSubgroupCentralPrimeTorsion

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {L : Type*} [Group L] {p a : ℕ} (P : Subgroup L)

theorem closure_setOf_inv_mul_inv_mul_mul_self_eq_commutator :
    Subgroup.closure {g : L | ∃ x ∈ P, ∃ y ∈ P, x⁻¹ * y⁻¹ * x * y = g} = ⁅P, P⁆ :=
  closure_setOf_inv_mul_inv_mul_mul P P

theorem mem_inf_centralizer_iff {z : L} :
    z ∈ P ⊓ centralizer (P : Set L) ↔ z ∈ P ∧ ∀ x ∈ P, z * x = x * z := by
  simp [Subgroup.mem_inf, mem_centralizer_iff, eq_comm]

theorem map_subtype_center_eq_inf_centralizer :
    (center ↥P).map P.subtype = P ⊓ centralizer (P : Set L) := by
  ext z
  simp only [mem_map, Subgroup.mem_inf, mem_center_iff, mem_centralizer_iff, coe_subtype]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, fun h hh => congrArg Subtype.val (hw ⟨h, hh⟩)⟩
  · rintro ⟨hz, hzc⟩
    exact ⟨⟨z, hz⟩, fun g => Subtype.ext (hzc g g.2), rfl⟩

theorem map_subtype_center_inf_commutator :
    ((center ↥P) ⊓ (_root_.commutator ↥P)).map P.subtype
      = (P ⊓ centralizer (P : Set L)) ⊓ ⁅P, P⁆ := by
  rw [Subgroup.map_inf _ _ _ P.subtype_injective, map_subtype_center_eq_inf_centralizer,
    Subgroup.map_subtype_commutator]

theorem subgroupOf_inf_centralizer_inf_commutator :
    ((P ⊓ centralizer (P : Set L)) ⊓ ⁅P, P⁆).subgroupOf P
      = (center ↥P) ⊓ (_root_.commutator ↥P) := by
  refine Subgroup.map_injective P.subtype_injective ?_
  rw [Subgroup.subgroupOf_map_subtype, map_subtype_center_inf_commutator,
    inf_eq_left.mpr (le_trans inf_le_left inf_le_left)]

theorem inf_centralizer_inf_commutator_le_inf_centralizer :
    (P ⊓ centralizer (P : Set L)) ⊓ ⁅P, P⁆ ≤ P ⊓ centralizer (P : Set L) := inf_le_left

theorem inf_centralizer_inf_commutator_le_commutator :
    (P ⊓ centralizer (P : Set L)) ⊓ ⁅P, P⁆ ≤ ⁅P, P⁆ := inf_le_right

theorem inf_centralizer_inf_commutator_ne_bot (hp : p.Prime) (hP : Nat.card ↥P = p ^ a)
    (hna : ¬ IsMulCommutative ↥P) :
    (P ⊓ centralizer (P : Set L)) ⊓ ⁅P, P⁆ ≠ ⊥ := by
  rw [← map_subtype_center_inf_commutator, Ne,
    Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective, inf_comm]
  exact inf_center_ne_bot (_root_.commutator ↥P) hp hP
    (fun h => hna ((commutator_eq_bot_iff ↥P).mp h))

theorem normal_inf_centralizer_inf_commutator [P.Normal] :
    ((P ⊓ centralizer (P : Set L)) ⊓ ⁅P, P⁆).Normal := by
  have : (((P ⊓ centralizer (P : Set L)) ⊓ ⁅P, P⁆).subgroupOf P).Characteristic := by
    rw [subgroupOf_inf_centralizer_inf_commutator]; infer_instance
  exact normal_of_characteristic_subgroupOf_of_normal (le_trans inf_le_left inf_le_left)

theorem inf_centralizer_inf_commutator_ne_bot_and_normal_and_le [P.Normal] (hp : p.Prime)
    (hP : Nat.card ↥P = p ^ a) (hna : ¬ IsMulCommutative ↥P) :
    ((P ⊓ centralizer (P : Set L)) ⊓ ⁅P, P⁆ ≠ ⊥) ∧
      ((P ⊓ centralizer (P : Set L)) ⊓ ⁅P, P⁆).Normal ∧
      (P ⊓ centralizer (P : Set L)) ⊓ ⁅P, P⁆ ≤ P ⊓ centralizer (P : Set L) ∧
      (P ⊓ centralizer (P : Set L)) ⊓ ⁅P, P⁆ ≤ ⁅P, P⁆ :=
  ⟨inf_centralizer_inf_commutator_ne_bot P hp hP hna, normal_inf_centralizer_inf_commutator P,
    inf_le_left, inf_le_right⟩

end CFSG.FeitThompson
