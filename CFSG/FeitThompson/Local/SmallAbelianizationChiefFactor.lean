module

public import Mathlib.GroupTheory.Complement
import CFSG.FeitThompson.Local.NormalKernelSectionOrderBound
public import CFSG.FeitThompson.Local.ChiefFactorIrreducibleModule
import CFSG.FeitThompson.Local.FixedFreeComplementNilpotentSections
import CFSG.FeitThompson.Foundations.SolvablePerfectTrivial
import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup

variable {L : Type*} [Group L] {H E : Subgroup L}

theorem commutator_self_subgroupOf_self : (⁅H, H⁆).subgroupOf H = _root_.commutator ↥H := by
  rw [Subgroup.subgroupOf, ← Subgroup.map_subtype_commutator,
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective]

theorem relIndex_commutator_self_eq_index_commutator :
    (⁅H, H⁆).relIndex H = (_root_.commutator ↥H).index := by
  rw [Subgroup.relIndex, commutator_self_subgroupOf_self]

instance normal_commutator_self_of_normal [H.Normal] : (⁅H, H⁆).Normal :=
  haveI : ((⁅H, H⁆).subgroupOf H).Characteristic := by
    rw [commutator_self_subgroupOf_self]; infer_instance
  normal_of_characteristic_subgroupOf_of_normal (Subgroup.commutator_le_self H)

theorem commutator_self_lt_self_of_isNilpotent (hH : H ≠ ⊥) [Group.IsNilpotent ↥H] :
    ⁅H, H⁆ < H := by
  refine lt_of_le_of_ne (Subgroup.commutator_le_self H) fun hc => ?_
  have h : (_root_.commutator ↥H).map H.subtype = (⊤ : Subgroup ↥H).map H.subtype := by
    rw [Subgroup.map_subtype_commutator, hc, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h2 : _root_.commutator ↥H = ⊤ := Subgroup.map_injective H.subtype_injective h
  exact absurd (subsingleton_of_isSolvable_of_commutator_eq_top ↥H h2)
    (not_subsingleton_iff_nontrivial.2 ((Subgroup.nontrivial_iff_ne_bot H).2 hH))

theorem not_lt_lt_commutator_self [Finite L] [H.Normal] [Group.IsNilpotent ↥H]
    (hL : Odd (Nat.card L))
    (hC : ∀ v ∈ E, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥)
    (hbd : (⁅H, H⁆).relIndex H ≤ 4 * Nat.card ↥E ^ 2 + 1)
    (J : Subgroup L) [J.Normal] (h₁ : ⁅H, H⁆ < J) (h₂ : J < H) : False := by
  have hlow : 2 * Nat.card ↥E + 1 ≤ (⁅H, H⁆).relIndex J :=
    two_mul_natCard_add_one_le_relIndex (H := H) (E := E) hL h₁ h₂.le hC
  have hhigh : 2 * Nat.card ↥E + 1 ≤ J.relIndex H :=
    two_mul_natCard_add_one_le_relIndex (H := H) (E := E) hL h₂ le_rfl hC
  have hmul : (⁅H, H⁆).relIndex J * J.relIndex H = (⁅H, H⁆).relIndex H :=
    Subgroup.relIndex_mul_relIndex _ _ _ h₁.le h₂.le
  have hepos : 0 < Nat.card ↥E := Nat.card_pos
  have hprod := Nat.mul_le_mul hlow hhigh
  rw [hmul] at hprod
  nlinarith [hprod, hbd, hepos]

theorem not_lt_lt_commutator_self_of_isComplement' [Finite L] [H.Normal] [Group.IsNilpotent ↥H]
    (hL : Odd (Nat.card L)) (hHE : H.IsComplement' E)
    (hC : ∀ v ∈ E, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥)
    (hbd : (⁅H, H⁆).relIndex H ≤ 4 * H.index ^ 2 + 1)
    (J : Subgroup L) [J.Normal] (h₁ : ⁅H, H⁆ < J) (h₂ : J < H) : False := by
  rw [index_eq_natCard_of_isComplement' hHE] at hbd
  exact not_lt_lt_commutator_self (E := E) hL hC hbd J h₁ h₂

theorem isChiefFactor_commutator_self [Finite L] [H.Normal] [Group.IsNilpotent ↥H]
    (hL : Odd (Nat.card L)) (hH : H ≠ ⊥)
    (hC : ∀ v ∈ E, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥)
    (hbd : (⁅H, H⁆).relIndex H ≤ 4 * Nat.card ↥E ^ 2 + 1) :
    IsChiefFactor H ⁅H, H⁆ where
  normal_num := ‹H.Normal›
  normal_den := inferInstance
  lt := commutator_self_lt_self_of_isNilpotent hH
  not_lt_lt _ _ h₁ h₂ := not_lt_lt_commutator_self (E := E) hL hC hbd _ h₁ h₂

theorem isChiefFactor_commutator_self_of_isComplement' [Finite L] [H.Normal]
    [Group.IsNilpotent ↥H] (hL : Odd (Nat.card L)) (hH : H ≠ ⊥) (hHE : H.IsComplement' E)
    (hC : ∀ v ∈ E, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥)
    (hbd : (⁅H, H⁆).relIndex H ≤ 4 * H.index ^ 2 + 1) :
    IsChiefFactor H ⁅H, H⁆ := by
  rw [index_eq_natCard_of_isComplement' hHE] at hbd
  exact isChiefFactor_commutator_self (E := E) hL hH hC hbd

theorem nontrivial_quotientFactor_commutator_self [Finite L] [H.Normal] [Group.IsNilpotent ↥H]
    (hL : Odd (Nat.card L)) (hH : H ≠ ⊥)
    (hC : ∀ v ∈ E, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥)
    (hbd : (⁅H, H⁆).relIndex H ≤ 4 * Nat.card ↥E ^ 2 + 1) :
    Nontrivial ↥(quotientFactor H ⁅H, H⁆) :=
  nontrivial_quotientFactor H _ (isChiefFactor_commutator_self (E := E) hL hH hC hbd).lt

theorem eq_bot_of_normal_lt_quotientFactor_commutator_self [Finite L] [H.Normal]
    [Group.IsNilpotent ↥H] (hL : Odd (Nat.card L)) (hH : H ≠ ⊥)
    (hC : ∀ v ∈ E, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥)
    (hbd : (⁅H, H⁆).relIndex H ≤ 4 * Nat.card ↥E ^ 2 + 1)
    (K : Subgroup (L ⧸ ⁅H, H⁆)) (hK : K.Normal) (hKlt : K < quotientFactor H ⁅H, H⁆) :
    K = ⊥ :=
  eq_bot_of_normal_lt_quotientFactor H _
    (isChiefFactor_commutator_self (E := E) hL hH hC hbd) K hK hKlt

end CFSG.FeitThompson
