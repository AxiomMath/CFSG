module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.FocalSubgroup
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem exists_complement_of_abelian_sylow {p : ℕ} [hp : Fact p.Prime] (S : Sylow p G)
    (hSab : ∀ x y : (S : Subgroup G), x * y = y * x) :
    ∃ R : Subgroup G, R ≤ (S : Subgroup G) ∧ R ⊓ commutator G = ⊥ ∧
      ((S : Subgroup G) ⊓ commutator G) ⊔ R = (S : Subgroup G) := by
  set N := Subgroup.normalizer ((S : Subgroup G) : Set G) with hNdef
  have hSN : (S : Subgroup G) ≤ N := Subgroup.le_normalizer
  set S' : Subgroup N := (S : Subgroup G).subgroupOf N with hS'def
  have hS'n : S'.Normal := Subgroup.normal_in_normalizer
  have hS'card : Nat.card S' = Nat.card (S : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
  have hS'idx : ¬ p ∣ S'.index := fun h =>
    S.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hSN))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hcop : (Nat.card S').Coprime S'.index := by
    rw [hS'card, hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hS'idx)
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set H : Subgroup G := K.map N.subtype with hHdef
  have hHN : H ≤ N := Subgroup.map_subtype_le K
  have hHcard : Nat.card H = S'.index := by
    rw [hHdef, Subgroup.card_map_of_injective N.subtype_injective]
    exact hK.symm.index_eq_card.symm
  have hHp : ¬ p ∣ Nat.card H := by
    rw [hHcard]
    exact hS'idx
  have hdecomp : ∀ n ∈ N, ∃ s ∈ (S : Subgroup G), ∃ h ∈ H, s * h = n := by
    intro n hn
    obtain ⟨⟨s, h⟩, hsh⟩ := (hK.existsUnique ⟨n, hn⟩).exists
    exact ⟨s, Subgroup.mem_subgroupOf.mp s.2, h, ⟨h, h.2, rfl⟩, congrArg Subtype.val hsh⟩
  have hfus : ∀ x ∈ (S : Subgroup G), ∀ g : G, g⁻¹ * x * g ∈ (S : Subgroup G) →
      ∃ h ∈ H, g⁻¹ * x * g = h⁻¹ * x * h := by
    intro x hx g hg
    haveI : IsMulCommutative (S : Subgroup G) := ⟨⟨hSab⟩⟩
    obtain ⟨n, hn, hgn⟩ := Sylow.conj_eq_normalizer_conj_of_mem S x g hx hg
    obtain ⟨s, hs, h, hh, rfl⟩ := hdecomp n hn
    refine ⟨h, hh, ?_⟩
    have hxs : x * s = s * x := congrArg Subtype.val (hSab ⟨x, hx⟩ ⟨s, hs⟩)
    rw [hgn]
    calc (s * h)⁻¹ * x * (s * h) = h⁻¹ * (s⁻¹ * (x * s)) * h := by group
      _ = h⁻¹ * x * h := by rw [hxs, inv_mul_cancel_left]
  have hfocal : (S : Subgroup G) ⊓ commutator G = ⁅(S : Subgroup G), H⁆ := by
    refine le_antisymm ?_ (le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hHN) ?_)
    · have h := CFSG.sylow_inf_derivedSubgroup_eq_focalSubgroup p S
      rw [CFSG.derivedSubgroup, derivedSeries_one] at h
      rw [h, Subgroup.closure_le]
      rintro z ⟨x, hx, y, hy, hxy, rfl⟩
      obtain ⟨c, hc⟩ := isConj_iff.mp hxy
      have hy' : c⁻¹⁻¹ * x * c⁻¹ = y := by rw [inv_inv]; exact hc
      obtain ⟨h, hh, hxh⟩ := hfus x hx c⁻¹ (by rw [hy']; exact hy)
      rw [← hy', hxh]
      have he : x⁻¹ * (h⁻¹ * x * h) = ⁅x⁻¹, h⁻¹⁆ := by
        rw [commutatorElement_def, inv_inv, inv_inv]
        group
      rw [he]
      exact Subgroup.commutator_mem_commutator ((S : Subgroup G).inv_mem hx) (H.inv_mem hh)
    · rw [_root_.commutator_def]
      exact Subgroup.commutator_mono le_top le_top
  have hcopHS : Nat.Coprime (Nat.card H) (Nat.card (S : Subgroup G)) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hHp).symm
  obtain ⟨hdsup, hddisj⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp (S : Subgroup G) H hHN hSab hcopHS
  refine ⟨(S : Subgroup G) ⊓ Subgroup.centralizer (H : Set G), inf_le_left, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    have hxc : x ∈ ⁅(S : Subgroup G), H⁆ := by
      rw [← hfocal]
      exact ⟨hx.1.1, hx.2⟩
    exact mem_bot.2 (Subgroup.disjoint_def.1 hddisj hx.1 hxc)
  · rw [hfocal, sup_comm]
    exact hdsup

theorem commutator_le_of_sup_eq_top {S N : Subgroup G} [N.Normal]
    (hSab : ∀ x y : S, x * y = y * x) (hN : N ⊔ S = ⊤) : commutator G ≤ N := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  have key : ∀ g : G, ∃ s ∈ S, QuotientGroup.mk' N g = QuotientGroup.mk' N s := by
    intro g
    obtain ⟨n, hn, s, hs, hns⟩ := mem_sup_of_normal_left.1 (hN ▸ mem_top g : g ∈ N ⊔ S)
    refine ⟨s, hs, ?_⟩
    rw [← hns, map_mul, show QuotientGroup.mk' N n = 1 from (QuotientGroup.eq_one_iff n).2 hn,
      one_mul]
  obtain ⟨s₁, hs₁, h₁⟩ := key g₁
  obtain ⟨s₂, hs₂, h₂⟩ := key g₂
  rw [← QuotientGroup.eq_one_iff]
  change QuotientGroup.mk' N ⁅g₁, g₂⁆ = 1
  rw [map_commutatorElement, h₁, h₂, ← map_commutatorElement]
  have : ⁅s₁, s₂⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (hSab ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩)
  rw [this, map_one]

theorem exists_complement_of_abelian_sylow_sup {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (hSab : ∀ x y : (S : Subgroup G), x * y = y * x) (N : Subgroup G) [N.Normal]
    (hN : N ⊔ (S : Subgroup G) = ⊤) (hperf : N ≤ commutator G) :
    ∃ R : Subgroup G, R ≤ (S : Subgroup G) ∧ R ⊓ N = ⊥ ∧
      ((S : Subgroup G) ⊓ N) ⊔ R = (S : Subgroup G) := by
  have hcomm : commutator G = N := le_antisymm (commutator_le_of_sup_eq_top hSab hN) hperf
  obtain ⟨R, hRS, hRc, hsup⟩ := exists_complement_of_abelian_sylow S hSab
  rw [hcomm] at hRc hsup
  exact ⟨R, hRS, hRc, hsup⟩

theorem exists_complement_of_abelian_sylow_amb {A : Type*} [Group A] [Finite A] {p : ℕ}
    [Fact p.Prime] (S : Sylow p A) (hSab : ∀ x y : (S : Subgroup A), x * y = y * x)
    (N : Subgroup A) [N.Normal] (hperf : ⁅N, N⁆ = N) :
    ∃ R : Subgroup A, R ≤ (S : Subgroup A) ∧ R ⊓ N = ⊥ ∧
      ((S : Subgroup A) ⊓ N) ⊔ R = (S : Subgroup A) := by
  classical
  set M : Subgroup A := N ⊔ (S : Subgroup A) with hM
  have hSM : (S : Subgroup A) ≤ M := le_sup_right
  have hNM : N ≤ M := le_sup_left
  let S₀ : Sylow p M := S.subtype hSM
  have hS₀ : (S₀ : Subgroup M) = (S : Subgroup A).subgroupOf M := S.coe_subtype hSM
  set N₀ : Subgroup M := N.subgroupOf M with hN₀
  have hmemS : ∀ g : M, g ∈ (S₀ : Subgroup M) ↔ (g : A) ∈ (S : Subgroup A) := fun g =>
    (SetLike.ext_iff.1 hS₀ g).trans mem_subgroupOf
  have hSab₀ : ∀ x y : (S₀ : Subgroup M), x * y = y * x := by
    intro x y
    have hx : ((x : M) : A) ∈ (S : Subgroup A) := (hmemS _).1 x.2
    have hy : ((y : M) : A) ∈ (S : Subgroup A) := (hmemS _).1 y.2
    have h := hSab ⟨((x : M) : A), hx⟩ ⟨((y : M) : A), hy⟩
    have h' : ((x : M) : A) * ((y : M) : A) = ((y : M) : A) * ((x : M) : A) :=
      congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hN₀top : N₀ ⊔ (S₀ : Subgroup M) = ⊤ := by
    refine eq_top_iff.2 fun g _ => ?_
    obtain ⟨n, hn, s, hs, hns⟩ := mem_sup_of_normal_left.1 g.2
    have h1 : (⟨n, hNM hn⟩ : M) ∈ N₀ := mem_subgroupOf.2 hn
    have h2 : (⟨s, hSM hs⟩ : M) ∈ (S₀ : Subgroup M) := (hmemS _).2 hs
    have := mul_mem_sup h1 h2
    have e : (⟨n, hNM hn⟩ : M) * ⟨s, hSM hs⟩ = g := Subtype.ext hns
    rwa [e] at this
  have hN₀perf : N₀ ≤ commutator M := by
    have h1 : ⁅N₀, N₀⁆ = N₀ := by
      refine Subgroup.map_injective M.subtype_injective ?_
      rw [Subgroup.map_commutator, hN₀, subgroupOf_map_subtype, inf_of_le_left hNM, hperf]
    calc N₀ = ⁅N₀, N₀⁆ := h1.symm
      _ ≤ commutator M := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mono le_top le_top
  obtain ⟨R₀, hR₀S, hR₀N, hsup₀⟩ :=
    exists_complement_of_abelian_sylow_sup S₀ hSab₀ N₀ hN₀top hN₀perf
  have hmapS : (S₀ : Subgroup M).map M.subtype = (S : Subgroup A) := by
    rw [hS₀, subgroupOf_map_subtype, inf_of_le_left hSM]
  have hmapN : N₀.map M.subtype = N := by
    rw [hN₀, subgroupOf_map_subtype, inf_of_le_left hNM]
  refine ⟨R₀.map M.subtype, ?_, ?_, ?_⟩
  · rw [← hmapS]
    exact Subgroup.map_mono hR₀S
  · rw [eq_bot_iff]
    rintro _ ⟨⟨r, hr, rfl⟩, hrN⟩
    have h1 : r ∈ N₀ := mem_subgroupOf.2 hrN
    have h2 : r ∈ R₀ ⊓ N₀ := ⟨hr, h1⟩
    rw [hR₀N, mem_bot] at h2
    subst h2
    simp
  · refine le_antisymm (sup_le inf_le_left ?_) fun x hx => ?_
    · rw [← hmapS]
      exact Subgroup.map_mono hR₀S
    · have hxM : x ∈ M := hSM hx
      have hg : (⟨x, hxM⟩ : M) ∈ (S₀ : Subgroup M) := (hmemS _).2 hx
      rw [← hsup₀] at hg
      have hmap : x ∈ ((S₀ : Subgroup M) ⊓ N₀ ⊔ R₀).map M.subtype := ⟨_, hg, rfl⟩
      rw [Subgroup.map_sup] at hmap
      have hle : ((S₀ : Subgroup M) ⊓ N₀).map M.subtype ≤ (S : Subgroup A) ⊓ N := by
        rintro _ ⟨s, ⟨hs₁, hs₂⟩, rfl⟩
        exact ⟨(hmemS s).1 hs₁, mem_subgroupOf.1 hs₂⟩
      exact (sup_le_sup_right hle _) hmap

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S
