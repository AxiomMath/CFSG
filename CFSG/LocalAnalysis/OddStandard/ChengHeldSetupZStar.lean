module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSetup
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStar

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

namespace Datum

variable (d : Datum A)

theorem exists_conj_ne (h : Hyp G A) :
    ∃ g : G, g⁻¹ * d.q * g ∈ d.X ∧ g⁻¹ * d.q * g ≠ d.q := by
  classical
  have := h.setting.simple
  by_contra hcon
  push Not at hcon
  obtain ⟨hqX, hXc⟩ := d.q_mem_X h
  obtain ⟨T, hXT⟩ := d.X_sylow.isPGroup.exists_le_sylow
  have hXT_eq : d.X = (T : Subgroup G) := by
    by_contra hne
    obtain ⟨g, hgT, hgN, hgX⟩ := exists_mem_normalizer_of_lt T.isPGroup' hXT hne
    have h1 : g⁻¹ * d.q * g ∈ d.X := (mem_normalizer_iff''.mp hgN d.q).mp hqX
    have h2 := hcon g h1
    have hgC : g ∈ centralizer ({d.q} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g * d.q = g * (g⁻¹ * d.q * g) := by rw [h2]
        _ = d.q * g := by group
    rw [d.centralizer_q h] at hgC
    have heq := d.X_sylow.eq_of_le (le_inf hXT d.X_sylow.le) inf_le_right
      (T.isPGroup'.to_inf_left (K := normalizer (A : Set G)))
    exact hgX (heq ▸ (mem_inf.mpr ⟨hgT, hgC⟩) : g ∈ d.X)
  have htT : d.q ∈ (T : Subgroup G) := hXT_eq ▸ hqX
  have hTc : ∀ s ∈ (T : Subgroup G), s * d.q = d.q * s := fun s hs =>
    mem_centralizer_singleton_iff.mp (hXc (hXT_eq ▸ hs))
  have hz2 : orderOf (⟨d.q, htT⟩ : (T : Subgroup G)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact d.q_ord
  have hzZ : (⟨d.q, htT⟩ : (T : Subgroup G)) ∈ center (T : Subgroup G) := by
    rw [mem_center_iff]
    intro s
    exact Subtype.ext (hTc s s.2)
  obtain ⟨hfac, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.glauberman_zStar_central_sylow_involution_univ
      T ⟨d.q, htT⟩ hzZ hz2 fun g hg => hcon g (hXT_eq ▸ hg)
  have hev : Even (Nat.card G) := by
    rw [even_iff_two_dvd, ← d.q_ord]
    exact orderOf_dvd_natCard d.q
  have hoddCore : Odd (Nat.card (CFSG.oddCore G)) := by
    have h2 : CFSG.oddCore G = CFSG.pPrimeCore 2 G := by
      simp only [CFSG.oddCore, CFSG.pPrimeCore, Nat.coprime_two_left]
    rw [h2]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := G))
  have hbot : CFSG.oddCore G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h1 | h1
    · exact h1
    · rw [h1, Subgroup.card_top] at hoddCore
      exact absurd hev (Nat.not_even_iff_odd.mpr hoddCore)
  have hqc : d.q ∈ center G := by
    rw [mem_center_iff]
    intro g
    obtain ⟨c, hc, k, hk, hgck⟩ := hfac g
    rw [hbot, mem_bot] at hk
    rw [hgck, hk, mul_one]
    exact mem_centralizer_singleton_iff.mp hc
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h1 | h1
  · rw [h1, mem_bot] at hqc
    have := d.q_ord
    rw [hqc, orderOf_one] at this
    exact absurd this (by norm_num)
  · obtain ⟨a, b, hab⟩ := h.setting.nonab
    exact hab (mem_center_iff.mp (h1 ▸ mem_top a) b).symm

end Datum

end CFSG.OddStandard.ChengHeld
