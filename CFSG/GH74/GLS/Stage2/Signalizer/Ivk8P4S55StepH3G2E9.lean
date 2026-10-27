module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import Mathlib.Algebra.Group.Pointwise.Set.Card

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3G2

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem isElementaryAbelian_sup_zpowers {x w : G} (hx3 : x ^ 3 = 1) (hw3 : w ^ 3 = 1)
    (hwx : w * x = x * w) : CFSG.IsElementaryAbelian 3 ↥(zpowers x ⊔ zpowers w) := by
  have := CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hx3
  have := CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hw3
  refine CFSG.IsElementaryAbelian.sup_of_le_centralizer ?_
  rw [zpowers_le, mem_centralizer_iff]
  intro y hy
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
  exact ((Commute.zpow_left (show Commute x w from hwx.symm) n).eq).symm.symm

theorem card_sup_zpowers [Finite G] {x w : G} (hx : orderOf x = 3) (hw3 : w ^ 3 = 1)
    (hwx : w * x = x * w) (hwn : w ∉ zpowers x) : Nat.card ↥(zpowers x ⊔ zpowers w) = 3 ^ 2 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hEA := isElementaryAbelian_sup_zpowers hx3 hw3 hwx
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
    (CFSG.IsElementaryAbelian.isPGroup 3 ↥(zpowers x ⊔ zpowers w))
  have hlt : zpowers x < zpowers x ⊔ zpowers w :=
    lt_of_le_of_ne le_sup_left fun h => hwn (h ▸ (le_sup_right : zpowers w ≤ _) (mem_zpowers w))
  have h1 : 3 < Nat.card ↥(zpowers x ⊔ zpowers w) := by
    have := card_lt_of_lt hlt
    rwa [Nat.card_zpowers, hx] at this
  have hnorm : zpowers x ≤ normalizer ((zpowers w : Subgroup G) : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro y
    have hc : ∀ n : ℤ, x * w ^ n * x⁻¹ = w ^ n := fun n => by
      rw [((Commute.zpow_right (show Commute x w from hwx.symm) n).eq), mul_inv_cancel_right]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, (hc n).symm⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have h2 : x * y * x⁻¹ = w ^ n := hn.symm
      calc w ^ n = x⁻¹ * (x * w ^ n * x⁻¹) * x := by group
        _ = x⁻¹ * (x * y * x⁻¹) * x := by rw [hc n, h2]
        _ = y := by group
  have hset : ((zpowers x ⊔ zpowers w : Subgroup G) : Set G) =
      (zpowers x : Set G) * (zpowers w : Set G) :=
    coe_mul_of_left_le_normalizer_right _ _ hnorm
  have hw' : Nat.card ↥(zpowers w) ≤ 3 :=
    Nat.le_of_dvd (by norm_num) (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hw3)
  have h2 : Nat.card ↥(zpowers x ⊔ zpowers w) ≤ 9 := by
    have h3 := Set.natCard_mul_le (s := (zpowers x : Set G)) (t := (zpowers w : Set G))
    rw [← hset] at h3
    have h4 : Nat.card ↥((zpowers x : Subgroup G) : Set G) = 3 := by
      change Nat.card ↥(zpowers x) = 3
      rw [Nat.card_zpowers, hx]
    have h5 : Nat.card ↥((zpowers w : Subgroup G) : Set G) ≤ 3 := hw'
    change Nat.card ↥(zpowers x ⊔ zpowers w) ≤ _ at h3
    rw [h4] at h3
    calc Nat.card ↥(zpowers x ⊔ zpowers w) ≤ 3 * Nat.card ↥((zpowers w : Subgroup G) : Set G) :=
          h3
      _ ≤ 3 * 3 := Nat.mul_le_mul_left 3 h5
  rw [hk] at h1 h2 ⊢
  have hk2 : k = 2 := by
    rcases Nat.lt_or_ge k 2 with hk' | hk'
    · interval_cases k <;> simp at h1
    · rcases Nat.eq_or_lt_of_le hk' with h | h
      · exact h.symm
      · have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
        omega
  rw [hk2]

theorem exists_commuting_of_order_three [Finite G] {E₀ : Subgroup G} (hcard : Nat.card E₀ = 9)
    (hexp : ∀ e ∈ E₀, e ^ 3 = 1) {x : G} (hx : orderOf x = 3) :
    ∃ w : G, w ^ 3 = 1 ∧ w * x = x * w ∧ w ∉ zpowers x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE₀p : IsPGroup 3 E₀ := IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)
  have hxp : IsPGroup 3 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hxP⟩ := hxp.exists_le_sylow
  obtain ⟨P₀, hE₀P₀⟩ := hE₀p.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P₀ P
  have hconj : ∀ e ∈ E₀, h * e * h⁻¹ ∈ (P : Subgroup G) := by
    intro e he
    rw [← hh, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem]
    have h1 : (MulAut.conj h)⁻¹ • (h * e * h⁻¹) = e := by
      change (MulAut.conj h)⁻¹ (h * e * h⁻¹) = e
      rw [MulAut.inv_apply, MulAut.conj_symm_apply]
      group
    rw [h1]
    exact hE₀P₀ he
  have hxPm : x ∈ (P : Subgroup G) := hxP (mem_zpowers x)
  by_cases hZ : ∀ y ∈ (P : Subgroup G), y * x = x * y
  ·
    have hex : ∃ e ∈ E₀, h * e * h⁻¹ ∉ zpowers x := by
      by_contra hcon
      push Not at hcon
      have hle : E₀.map (MulAut.conj h).toMonoidHom ≤ zpowers x := by
        rintro _ ⟨e, he, rfl⟩
        exact hcon e he
      have h1 := Subgroup.card_le_of_le hle
      rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hcard, Nat.card_zpowers,
        hx] at h1
      omega
    obtain ⟨e, he, hew⟩ := hex
    refine ⟨h * e * h⁻¹, ?_, hZ _ (hconj e he), hew⟩
    rw [conj_pow, hexp e he, mul_one, mul_inv_cancel]
  ·
    push Not at hZ
    obtain ⟨y, hyP, hyx⟩ := hZ
    have hx1 : x ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hx
      omega
    have : Nontrivial ↥(P : Subgroup G) :=
      ⟨⟨⟨x, hxPm⟩, 1, fun h1 => hx1 (congrArg Subtype.val h1)⟩⟩
    have hPp : IsPGroup 3 ↥(P : Subgroup G) := P.isPGroup'
    have hZnt := hPp.center_nontrivial
    have hZp : IsPGroup 3 ↥(center ↥(P : Subgroup G)) := hPp.to_subgroup _
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hZp
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne' hm
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥(P : Subgroup G))) 3
      (by rw [hm]; exact dvd_pow_self 3 hm0)
    have hwc : ∀ z : ↥(P : Subgroup G), z * (w : ↥(P : Subgroup G)) = (w : ↥(P : Subgroup G)) * z :=
      fun z => mem_center_iff.mp w.2 z
    have hwo : orderOf ((w : ↥(P : Subgroup G)) : G) = 3 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
    refine ⟨((w : ↥(P : Subgroup G)) : G), ?_, ?_, fun hwx => ?_⟩
    · have h1 := pow_orderOf_eq_one ((w : ↥(P : Subgroup G)) : G)
      rwa [hwo] at h1
    · have := hwc ⟨x, hxPm⟩
      exact (congrArg Subtype.val this).symm
    ·
      have hle : zpowers ((w : ↥(P : Subgroup G)) : G) ≤ zpowers x := zpowers_le.mpr hwx
      have heq : zpowers ((w : ↥(P : Subgroup G)) : G) = zpowers x :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hwo])
      have hxw : x ∈ zpowers ((w : ↥(P : Subgroup G)) : G) := heq ▸ mem_zpowers x
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hxw
      apply hyx
      have hwy : y * ((w : ↥(P : Subgroup G)) : G) = ((w : ↥(P : Subgroup G)) : G) * y :=
        congrArg Subtype.val (hwc ⟨y, hyP⟩)
      rw [← hn]
      exact (Commute.zpow_right (show Commute y _ from hwy) n).eq

theorem exists_plane_through [Finite G] {E₀ : Subgroup G} (hcard : Nat.card E₀ = 9)
    (hexp : ∀ e ∈ E₀, e ^ 3 = 1) {x : G} (hx : orderOf x = 3) :
    ∃ E : Subgroup G, x ∈ E ∧ CFSG.IsElementaryAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  obtain ⟨w, hw3, hwx, hwn⟩ := exists_commuting_of_order_three hcard hexp hx
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  exact ⟨zpowers x ⊔ zpowers w, (le_sup_left : zpowers x ≤ _) (mem_zpowers x),
    isElementaryAbelian_sup_zpowers hx3 hw3 hwx, card_sup_zpowers hx hw3 hwx hwn⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3G2
