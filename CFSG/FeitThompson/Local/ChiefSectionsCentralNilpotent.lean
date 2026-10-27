module

public import CFSG.FeitThompson.Local.ChiefFactorCentralizationCentralSeries
import CFSG.FeitThompson.Local.NormalNilpotentCentralizesChiefFactors
import CFSG.FeitThompson.Foundations.SolvableSubgroupSolvable

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup QuotientGroup

variable {L : Type*} [Group L]

theorem map_subgroupOf_le_center_iff {H A B : Subgroup L} (hAH : A ≤ H) [B.Normal] :
    (A.subgroupOf H).map (mk' (B.subgroupOf H)) ≤ center (↥H ⧸ B.subgroupOf H) ↔ ⁅H, A⁆ ≤ B := by
  rw [Subgroup.map_le_iff_le_comap, ← Subgroup.upperCentralSeriesStep_eq_comap_center,
    Subgroup.commutator_comm, Subgroup.commutator_le]
  constructor
  · intro hle a ha x hx
    have ha' : (⟨a, hAH ha⟩ : ↥H) ∈ A.subgroupOf H := by rwa [Subgroup.mem_subgroupOf]
    have h2 := (Subgroup.mem_upperCentralSeriesStep _ _).1 (hle ha') ⟨x, hx⟩
    rw [Subgroup.mem_subgroupOf] at h2
    simpa [commutatorElement_def] using h2
  · intro hle u hu
    rw [Subgroup.mem_upperCentralSeriesStep]
    intro v
    rw [Subgroup.mem_subgroupOf]
    have := hle u (by rwa [Subgroup.mem_subgroupOf] at hu) v v.2
    simpa [commutatorElement_def] using this

variable [Finite L] {H A B : Subgroup L}

theorem commutator_le_of_isChiefFactor_of_le (hH : H.Normal) (hnil : Group.IsNilpotent H)
    (h : IsChiefFactor A B) (hAH : A ≤ H) : ⁅H, A⁆ ≤ B :=
  haveI := hnil
  haveI : Group.IsSolvable ↥A := isSolvable_of_le (K := H) hAH
  commutator_le_of_isChiefFactor_of_isSolvable hH hnil h

theorem commutator_le_of_forall_normal_not_lt_lt (hH : H.Normal) (hnil : Group.IsNilpotent H)
    [A.Normal] [B.Normal] (hAH : A ≤ H) (hBA : B < A)
    (hchief : ∀ J : Subgroup L, J.Normal → B < J → ¬J < A) : ⁅H, A⁆ ≤ B :=
  commutator_le_of_isChiefFactor_of_le hH hnil ⟨‹A.Normal›, ‹B.Normal›, hBA, hchief⟩ hAH

theorem map_subgroupOf_le_center_of_forall_normal_not_lt_lt (hH : H.Normal)
    (hnil : Group.IsNilpotent H) [A.Normal] [B.Normal] (hAH : A ≤ H) (hBA : B < A)
    (hchief : ∀ J : Subgroup L, J.Normal → B < J → ¬J < A) :
    (A.subgroupOf H).map (mk' (B.subgroupOf H)) ≤ center (↥H ⧸ B.subgroupOf H) :=
  (map_subgroupOf_le_center_iff hAH).2
    (commutator_le_of_forall_normal_not_lt_lt hH hnil hAH hBA hchief)

theorem inv_mul_inv_mul_mul_mem_of_forall_normal_not_lt_lt (hH : H.Normal)
    (hnil : Group.IsNilpotent H) [A.Normal] [B.Normal] (hAH : A ≤ H) (hBA : B < A)
    (hchief : ∀ J : Subgroup L, J.Normal → B < J → ¬J < A) {a x : L} (ha : a ∈ H)
    (hx : x ∈ A) : a⁻¹ * x⁻¹ * a * x ∈ B := by
  have hmem := Subgroup.commutator_mem_commutator (H.inv_mem ha) (A.inv_mem hx)
  rw [commutatorElement_def, inv_inv, inv_inv] at hmem
  exact commutator_le_of_forall_normal_not_lt_lt hH hnil hAH hBA hchief hmem

end

end CFSG.FeitThompson
