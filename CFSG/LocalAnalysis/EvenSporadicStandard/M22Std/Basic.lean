module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.M22
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Center
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two {X : Type*} [Group X] {z c : X}
    (hz : orderOf z = 2) (hc : c ∈ zpowers z) : c = 1 ∨ c = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, ← hz]; exact pow_orderOf_eq_one z
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    obtain ⟨m, hm⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
    rw [hm, zpow_mul, h2, one_zpow]
  · right
    obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
    rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

section Frattini

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_sup_centralizer_of_centralizer_le {L : Subgroup G}
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hinn : centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G)) :
    normalizer (L : Set G) ≤ L ⊔ centralizer (L : Set G) := by
  intro g hg
  set C := centralizer (L : Set G) with hC
  have hgL : ∀ x : G, x ∈ L ↔ g * x * g⁻¹ ∈ L := fun x => Subgroup.mem_normalizer_iff.1 hg x
  have hgC : ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro c hc
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : g⁻¹ * x * g ∈ L := by
      rw [hgL (g⁻¹ * x * g)]
      have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [this]; exact hx
    have h1 := mem_centralizer_iff.1 hc _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * x := by group
  set t' : G := g * t * g⁻¹ with ht'def
  have ht'C : t' ∈ C := hgC t ht
  have ht'2 : orderOf t' = 2 := by
    rw [ht'def, show g * t * g⁻¹ = MulAut.conj g t from rfl, MulEquiv.orderOf_eq, ht2]
  let tC : C := ⟨t, ht⟩
  let tC' : C := ⟨t', ht'C⟩
  have htC : orderOf tC = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  have htC' : orderOf tC' = 2 := by rw [Subgroup.orderOf_mk]; exact ht'2
  obtain ⟨P1, hP1⟩ := exists_sylow_eq_zpowers hS htC
  obtain ⟨P2, hP2⟩ := exists_sylow_eq_zpowers hS htC'
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C P1 P2
  have hcmem : c * tC * c⁻¹ ∈ (P2 : Subgroup C) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    refine (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨tC, ?_, by simp [MulAut.conj_apply]⟩
    rw [hP1]; exact mem_zpowers _
  rw [hP2] at hcmem
  have hne : c * tC * c⁻¹ ≠ 1 := by
    intro h1
    have : tC = 1 := by simpa using h1
    rw [this, orderOf_one] at htC
    exact absurd htC (by decide)
  have hct : (c : G) * t * (c : G)⁻¹ = t' := by
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two htC' hcmem with h | h
    · exact absurd h hne
    · exact congrArg Subtype.val h
  have hcg : (c : G)⁻¹ * g ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : (c : G)⁻¹ * t' * (c : G) = t := by
      rw [← hct]; group
    calc (c : G)⁻¹ * g * t = ((c : G)⁻¹ * (g * t * g⁻¹) * (c : G)) * ((c : G)⁻¹ * g) := by group
      _ = t * ((c : G)⁻¹ * g) := by rw [← ht'def, h1]
  have h2 := hinn hcg
  have hcL : (c : G) ∈ L ⊔ C := (le_sup_right : C ≤ L ⊔ C) c.2
  have : g = (c : G) * ((c : G)⁻¹ * g) := by group
  rw [this]
  exact mul_mem hcL h2

end Frattini

section Simple

variable {G : Type} [Group G]

theorem standardComponentOddCore_eq_bot_of_simple [Finite G] [IsSimpleGroup G]
    (heven : Even (Nat.card G)) : standardComponentOddCore G = ⊥ := by
  refine le_antisymm (sSup_le fun N hN => ?_) bot_le
  have := hN.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h ▸ le_rfl
  · exfalso
    have h1 := hN.2
    rw [h, Subgroup.card_top] at h1
    exact (Nat.not_even_iff_odd.2 h1) heven

end Simple

theorem center_eq_bot_of_isSporadic
    {Y : Type} [Group Y] (hY : IsSporadic Y .M22) : center Y = ⊥ := by
  obtain ⟨e₀⟩ := hY
  have e : Y ≃* NativeSporadic.M22 := e₀
  exact HypOne.center_eq_bot_of_mulEquiv e.symm CFSG.Sporadic.Schreier.m22_center_eq_bot'

theorem innAut_index_dvd_two
    {Y : Type} [Group Y] [Finite Y] (hY : IsSporadic Y .M22) :
    (CFSG.EvenSporadicStandard.Finkelstein77.innAut Y).index ∣ 2 := by
  have hc := center_eq_bot_of_isSporadic hY
  obtain ⟨e₀⟩ := hY
  have e : Y ≃* NativeSporadic.M22 := e₀
  refine HypOne.index_dvd_two_of_card_le (HypOne.conj_injective_of_center_eq_bot hc) ?_
  calc Nat.card (MulAut Y) = Nat.card (MulAut NativeSporadic.M22) :=
        Nat.card_congr (MulAut.congr e).toEquiv
    _ ≤ 2 * Nat.card NativeSporadic.M22 := CFSG.Sporadic.Schreier.m22_mulAut_card
    _ = 2 * Nat.card Y := by rw [Nat.card_congr e.toEquiv]

theorem isSporadic_quotient_of_center_eq_bot {Y : Type} [Group Y] (h : center Y = ⊥)
    {s : TauCeti.SporadicName} (hs : IsSporadic Y s) : IsSporadic (Y ⧸ center Y) s := by
  obtain ⟨e⟩ := hs
  exact ⟨((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).trans e⟩

section Layer0

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem card_sylow_eq_two_of_isSporadic
    (h : StdHyp G L) (hL : IsSporadic L .M22) (S : Sylow 2 (centralizer (L : Set G))) :
    Nat.card S = 2 := by
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic hL
  have hq : IsSporadic (L ⧸ center L) .M22 := isSporadic_quotient_of_center_eq_bot hZ hL
  have hfull := HypOne.M22.fullRowData_of_isSporadic hq
  exact h.card_sylow_eq_two_of_fours hfull.rowData.hypothesisOne
    (HypOne.M22.foursGroupCondition_of_isSporadic hL) S

theorem relIndex_dvd_two
    (h : StdHyp G L) (hL : IsSporadic L .M22) {t : G} (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) :
    (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) ∣ 2 := by
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic hL
  have hq : IsSporadic (L ⧸ center L) .M22 := isSporadic_quotient_of_center_eq_bot hZ hL
  exact (h.relIndex_sup_zpowers_dvd (card_sylow_eq_two_of_isSporadic h hL) ht ht2).trans
    (innAut_index_dvd_two hq)

end Layer0

end CFSG.EvenSporadicStandard.M22Std
