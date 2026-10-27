module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowExtra
public import CFSG.Monster.B.Cbar.LocalStructure
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.General

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Monster.B

theorem xbar_mul_self : xbar * xbar = 1 := by
  rw [← pow_two, ← orderOf_xbar]
  exact pow_orderOf_eq_one xbar

theorem commutator_mem_center_aux {E : Type*} [Group E] (h : commutator E = center E) (a b : E) :
    a * b * a⁻¹ * b⁻¹ ∈ center E := by
  rw [← h, _root_.commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)

theorem ebar_comm_xbar {q : Cbar} (hq : q ∈ Ebar) : q * xbar = xbar * q := by
  have hx : xbar ∈ (Subgroup.center Ebar).map Ebar.subtype := by
    rw [map_center_Ebar]
    exact Subgroup.mem_zpowers xbar
  obtain ⟨z, hz, hzx⟩ := hx
  have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨q, hq⟩)
  rw [← hzx]
  change q * (z : Cbar) = (z : Cbar) * q
  simpa using h

theorem ebar_center {q : Cbar} (hq : q ∈ Ebar) (h : ∀ y ∈ Ebar, q * y = y * q) :
    q = 1 ∨ q = xbar := by
  have hc : (⟨q, hq⟩ : Ebar) ∈ Subgroup.center Ebar :=
    Subgroup.mem_center_iff.2 fun y => Subtype.ext (h y.1 y.2).symm
  have hm : q ∈ (Subgroup.center Ebar).map Ebar.subtype := ⟨⟨q, hq⟩, hc, rfl⟩
  rw [map_center_Ebar] at hm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
  rcases zpow_eq_one_or_self_of_orderOf_eq_two orderOf_xbar k with h1 | h1
  · exact Or.inl (hk.symm.trans h1)
  · exact Or.inr (hk.symm.trans h1)

theorem ebar_comm {a b : Cbar} (ha : a ∈ Ebar) (hb : b ∈ Ebar) :
    a * b = b * a ∨ a * b = xbar * (b * a) := by
  have hc := commutator_mem_center_aux (E := Ebar) Ebar_extraspecial.1.2.1 ⟨a, ha⟩ ⟨b, hb⟩
  have hm : a * b * a⁻¹ * b⁻¹ ∈ (Subgroup.center Ebar).map Ebar.subtype := ⟨_, hc, rfl⟩
  rw [map_center_Ebar] at hm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
  have e : a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
  rcases zpow_eq_one_or_self_of_orderOf_eq_two orderOf_xbar k with h1 | h1
  · left
    rw [e, ← hk, h1, one_mul]
  · right
    rw [e, ← hk, h1]

theorem ebar_centralizer {c : Cbar}
    (h : ∀ q ∈ Ebar, c * q = q * c) : c ∈ Ebar := by
  have hcx : c ∈ Subgroup.centralizer ({xbar} : Set Cbar) :=
    Subgroup.mem_centralizer_singleton_iff.2 (h xbar xbar_mem_Ebar)
  rw [centralizer_xbar] at hcx
  have hc : c ∈ Jbar ⊓ Subgroup.centralizer (Ebar : Set Cbar) :=
    ⟨hcx, Subgroup.mem_centralizer_iff.2 fun q hq => (h q hq).symm⟩
  rw [centralizer_Ebar] at hc
  exact (Subgroup.zpowers_le.2 xbar_mem_Ebar) hc

theorem eq_of_commute_ebar_centralizer {w g : Cbar}
    (hw : w ∈ Ebar) (hw2 : w * w = 1) (hgx : g * xbar = xbar * g)
    (hgT : ∀ t ∈ Ebar, w * t = t * w → g * t = t * g) :
    g = 1 ∨ g = xbar ∨ g = w ∨ g = xbar * w := by
  have hgJ : g ∈ Jbar := by
    rw [← centralizer_xbar]
    exact Subgroup.mem_centralizer_singleton_iff.2 hgx
  refine eq_of_normalizes_centralizer_extraspecial Ebar xbar_mul_self ?_
    (fun q hq => ebar_comm_xbar hq) (fun q hq h => ebar_center hq h)
    (fun a ha b hb => ebar_comm ha hb) hw hw2 (fun c hc => ebar_centralizer hc) ?_ hgx hgT
  · intro h
    have := orderOf_xbar
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  · intro q hq
    have h := conj_mem_Ebar (Jbar.inv_mem hgJ) hq
    rwa [inv_inv] at h

end CFSG.EvenSporadicStandard.Solomon78
