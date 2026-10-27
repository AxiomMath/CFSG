module

public import CFSG.GH74.Uniqueness.SU.SU13TA9PermE
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverLift

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup CFSG.LocalAnalysis.ComponentInitial

@[expose] def Mb : Subgroup (alternatingGroup (Fin 9)) :=
  centralizer ({ea * eb} : Set (alternatingGroup (Fin 9)))

theorem card_Mb : Nat.card Mb = 54 := card_centralizer_ea_mul_eb

theorem mem_Mb_iff {y : alternatingGroup (Fin 9)} :
    y ∈ Mb ↔ Commute (y : Perm (Fin 9)) (pa * pb) := by
  rw [Mb, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (congrArg Subtype.val h : (y : Perm (Fin 9)) * (pa * pb) = pa * pb * y)
  · intro h
    exact Subtype.ext h.eq

theorem Ebar_le_Mb : Ebar ≤ Mb := by
  intro x hx
  obtain ⟨ha, hb, -⟩ := mem_Ebar_iff.mp hx
  rw [mem_Mb_iff]
  exact ha.mul_right hb

theorem et_mem_Mb : et ∈ Mb := by
  rw [mem_Mb_iff]
  show pt * (pa * pb) = pa * pb * pt
  decide

theorem et_not_mem_Ebar : et ∉ Ebar := by
  intro h
  have h2 : pt * pa = pa * pt := (mem_Ebar_iff.mp h).1.eq
  revert h2
  decide

theorem relIndex_Ebar_Mb : Ebar.relIndex Mb = 2 := by
  have h := Subgroup.relIndex_mul_card (H := Ebar) (K := Mb)
  rw [inf_of_le_left Ebar_le_Mb, card_Ebar, card_Mb] at h
  omega

theorem conj_mem_Ebar {y x : alternatingGroup (Fin 9)} (hy : y ∈ Mb) (hx : x ∈ Ebar) :
    y * x * y⁻¹ ∈ Ebar := by
  have hN : (Ebar.subgroupOf Mb).Normal := Subgroup.normal_of_index_eq_two relIndex_Ebar_Mb
  have h := hN.conj_mem ⟨x, Ebar_le_Mb hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨y, hy⟩
  exact Subgroup.mem_subgroupOf.mp h

theorem toP_diag_zero : ∀ j : Fin 3, toP j j 0 = (pa * pb) ^ (j : ℕ) := by decide

theorem mem_Ebar_of_odd_orderOf {y : alternatingGroup (Fin 9)} (hy : y ∈ Mb)
    (ho : Odd (orderOf y)) : y ∈ Ebar := by
  have hsq : y ^ 2 ∈ Ebar := by
    have := Subgroup.sq_mem_of_index_two (H := Ebar.subgroupOf Mb) relIndex_Ebar_Mb ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨m, hm⟩ := ho
  have h1 : y ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one y
  have : y = (y ^ 2) ^ (m + 1) := by
    calc y = y ^ (2 * m + 1) * y := by rw [h1, one_mul]
      _ = (y ^ 2) ^ (m + 1) := by rw [← pow_mul, ← pow_succ]; congr 1
  rw [this]
  exact Subgroup.pow_mem _ hsq _

theorem neg_eq_self_fin_three : ∀ k : Fin 3, -k = k → k = 0 := by decide

theorem mem_zpowers_of_commute_et {x : alternatingGroup (Fin 9)} (hx : x ∈ Ebar)
    (hc : et * x = x * et) : x ∈ zpowers (ea * eb) := by
  obtain ⟨i, j, k, rfl⟩ := mem_Ebar_iff_toE.mp hx
  have h1 : pt * toP i j k * pt⁻¹ = toP i j k := by
    have : pt * toP i j k = toP i j k * pt := congrArg Subtype.val hc
    rw [this]
    group
  rw [pt_mul_toP] at h1
  obtain ⟨hij, hji, hk⟩ := toP_injective h1
  subst hij
  have hk0 : k = 0 := neg_eq_self_fin_three k hk
  subst hk0
  refine ⟨(j : ℤ), Subtype.ext ?_⟩
  show ((ea * eb : alternatingGroup (Fin 9)) ^ (j : ℤ) : alternatingGroup (Fin 9)).val = toP j j 0
  rw [zpow_natCast, Subgroup.coe_pow]
  exact (toP_diag_zero j).symm

theorem ea_mul_eb_mem_Ebar : ea * eb ∈ Ebar := Subgroup.mul_mem _ ea_mem_Ebar eb_mem_Ebar

theorem ea_mul_eb_inv_mem_Ebar : ea * eb⁻¹ ∈ Ebar :=
  Subgroup.mul_mem _ ea_mem_Ebar (Subgroup.inv_mem _ eb_mem_Ebar)

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
