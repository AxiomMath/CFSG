module

public import Mathlib.GroupTheory.Complement
import CFSG.FeitThompson.OddOrder.FrobeniusKernelContainsCentralizers

open Subgroup Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] {L H E : Subgroup G}

theorem left_le_of_coe_mul_coe_eq (hmul : (H : Set G) * (E : Set G) = (L : Set G)) : H ≤ L := by
  intro x hx
  have hx' : x ∈ (H : Set G) * (E : Set G) := ⟨x, hx, 1, E.one_mem, mul_one x⟩
  rwa [hmul] at hx'

theorem right_le_of_coe_mul_coe_eq (hmul : (H : Set G) * (E : Set G) = (L : Set G)) : E ≤ L := by
  intro x hx
  have hx' : x ∈ (H : Set G) * (E : Set G) := ⟨1, H.one_mem, x, hx, one_mul x⟩
  rwa [hmul] at hx'

theorem isComplement'_subgroupOf_of_coe_mul_coe_eq
    (hmul : (H : Set G) * (E : Set G) = (L : Set G)) (hdisj : H ⊓ E = ⊥) :
    (H.subgroupOf L).IsComplement' (E.subgroupOf L) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ H ⊓ E := ⟨hx.1, hx.2⟩
    rw [hdisj, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.2 (Subtype.ext hx')
  · refine Set.eq_univ_of_forall fun x => ?_
    have hxL : (x : G) ∈ (H : Set G) * (E : Set G) := by rw [hmul]; exact x.2
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hxL
    exact Set.mem_mul.2 ⟨⟨a, left_le_of_coe_mul_coe_eq hmul ha⟩, ha,
      ⟨b, right_le_of_coe_mul_coe_eq hmul hb⟩, hb, Subtype.ext hab⟩

theorem inf_centralizer_singleton_subgroupOf_eq_bot
    (hC : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set G) = ⊥)
    {e : L} (he : e ∈ E.subgroupOf L) (he1 : e ≠ 1) :
    H.subgroupOf L ⊓ centralizer ({e} : Set L) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxc : (x : G) * (e : G) = (e : G) * (x : G) := by
    simpa using Subtype.ext_iff.1 (mem_centralizer_singleton_iff.1 hx.2)
  have hx' : (x : G) ∈ H ⊓ centralizer ({(e : G)} : Set G) :=
    ⟨hx.1, mem_centralizer_singleton_iff.mpr hxc⟩
  rw [hC (e : G) he (fun h => he1 (Subtype.ext (by simpa using h))), Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.2 (Subtype.ext hx')

theorem centralizer_singleton_le_left [Finite H] [(H.subgroupOf L).Normal]
    (hmul : (H : Set G) * (E : Set G) = (L : Set G)) (hdisj : H ⊓ E = ⊥)
    (hCH : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set G) = ⊥)
    (hCG : ∀ h ∈ H, h ≠ 1 → centralizer ({h} : Set G) ≤ L)
    {h : G} (hh : h ∈ H) (hh1 : h ≠ 1) : centralizer ({h} : Set G) ≤ H := by
  have hHL : H ≤ L := left_le_of_coe_mul_coe_eq hmul
  have : Finite (H.subgroupOf L) :=
    Finite.of_equiv _ (Subgroup.subgroupOfEquivOfLe hHL).symm.toEquiv
  have hh'1 : (⟨h, hHL hh⟩ : L) ≠ 1 := fun he => hh1 (by simpa using Subtype.ext_iff.1 he)
  have key := centralizer_singleton_le_of_mem_of_ne_one
    (isComplement'_subgroupOf_of_coe_mul_coe_eq hmul hdisj)
    (fun e he he1 => inf_centralizer_singleton_subgroupOf_eq_bot hCH he he1)
    (h := (⟨h, hHL hh⟩ : L)) hh hh'1
  intro y hy
  have hmemc : (⟨y, hCG h hh hh1 hy⟩ : L) ∈ centralizer ({(⟨h, hHL hh⟩ : L)} : Set L) :=
    mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.1 hy))
  exact key hmemc

theorem mem_of_pow_mem_of_ne_one [Finite H] [(H.subgroupOf L).Normal]
    (hmul : (H : Set G) * (E : Set G) = (L : Set G)) (hdisj : H ⊓ E = ⊥)
    (hCH : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set G) = ⊥)
    (hCG : ∀ h ∈ H, h ≠ 1 → centralizer ({h} : Set G) ≤ L)
    {g : G} {n : ℕ} (hgn : g ^ n ∈ H) (hgn1 : g ^ n ≠ 1) : g ∈ H :=
  centralizer_singleton_le_left hmul hdisj hCH hCG hgn hgn1
    (mem_centralizer_singleton_iff.mpr (Commute.self_pow g n))

theorem mem_of_zpow_mem_of_ne_one [Finite H] [(H.subgroupOf L).Normal]
    (hmul : (H : Set G) * (E : Set G) = (L : Set G)) (hdisj : H ⊓ E = ⊥)
    (hCH : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set G) = ⊥)
    (hCG : ∀ h ∈ H, h ≠ 1 → centralizer ({h} : Set G) ≤ L)
    {g : G} {n : ℤ} (hgn : g ^ n ∈ H) (hgn1 : g ^ n ≠ 1) : g ∈ H := by
  have key : g ^ n.natAbs ∈ H ∧ g ^ n.natAbs ≠ 1 := by
    rcases Int.natAbs_eq n with hn | hn
    · rw [← zpow_natCast, ← hn]; exact ⟨hgn, hgn1⟩
    · have hn' : ((n.natAbs : ℤ)) = -n := by omega
      rw [← zpow_natCast, hn', zpow_neg]
      exact ⟨H.inv_mem hgn, fun hh => hgn1 (inv_eq_one.mp hh)⟩
  exact mem_of_pow_mem_of_ne_one hmul hdisj hCH hCG key.1 key.2

theorem zpowers_le_of_pow_mem_of_ne_one [Finite H] [(H.subgroupOf L).Normal]
    (hmul : (H : Set G) * (E : Set G) = (L : Set G)) (hdisj : H ⊓ E = ⊥)
    (hCH : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set G) = ⊥)
    (hCG : ∀ h ∈ H, h ≠ 1 → centralizer ({h} : Set G) ≤ L)
    {g : G} {n : ℕ} (hgn : g ^ n ∈ H) (hgn1 : g ^ n ≠ 1) : zpowers g ≤ H :=
  zpowers_le.2 (mem_of_pow_mem_of_ne_one hmul hdisj hCH hCG hgn hgn1)

end

end CFSG.FeitThompson
