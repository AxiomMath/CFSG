module

public import CFSG.GH74.GLS.C3.Layer1.Defs

import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Sylow
import CFSG.LocalAnalysis.ComponentClassification.Walter86.GLSPumpupFoote

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.GH74.GLS CFSG.ABGLocalTools
open CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

theorem mem_centralizerSection_of_centralizes_sylow_of_isL34Quotient
    {G : Type} [Group G] [Finite G]
    (K P : Subgroup G) (g : G)
    (hK : ⁅K, K⁆ = K)
    (hL34 : IsL34Quotient (kBar K))
    (hZ : ∃ c ∈ center (kBar K), c * c ≠ 1)
    (hP : IsSylowOf 2 P K)
    (hgN : g ∈ normalizer (K : Set G))
    (hgP : ∀ p ∈ P, g * p = p * g) :
    g ∈ centralizerSection K (pPrimeCoreOf 2 K) := by
  have hP2 : IsSylowTwoIn P K := ⟨hP.le, hP.exists_sylow_eq_subgroupOf⟩
  have hL : IsL34Type (K ⧸ CFSG.Open.fusionZStar K) :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      (CFSG.ComponentClassification.Sol78.coreQuotientCenterEquiv ↥K) hL34
  obtain ⟨k, hkP, hkv, _⟩ := sylowCentralizer G K P g hK hL hP2 hgN hgP
  have hkK : k ∈ K := hP.le hkP
  have hkcommP : ∀ p ∈ P, k * p = p * k := by
    intro p hp
    have hgk : g * k = k * g := hgP k hkP
    have hx : k⁻¹ * g = g * k⁻¹ := by
      calc k⁻¹ * g = k⁻¹ * g * k * k⁻¹ := by group
        _ = k⁻¹ * (g * k) * k⁻¹ := by group
        _ = k⁻¹ * (k * g) * k⁻¹ := by rw [hgk]
        _ = g * k⁻¹ := by group
    have hgp' : g⁻¹ * p * g = p := by
      rw [mul_assoc, ← hgP p hp]
      group
    have hr : p⁻¹ * (k⁻¹ * g)⁻¹ * p * (k⁻¹ * g) = p⁻¹ * k * p * k⁻¹ := by
      rw [hx]
      calc p⁻¹ * (g * k⁻¹)⁻¹ * p * (g * k⁻¹)
          = p⁻¹ * k * (g⁻¹ * p * g) * k⁻¹ := by group
        _ = p⁻¹ * k * p * k⁻¹ := by rw [hgp']
    have hvo : p⁻¹ * (k⁻¹ * g)⁻¹ * p * (k⁻¹ * g) ∈ oddIn K := by
      show p⁻¹ * (k⁻¹ * g)⁻¹ * p * (k⁻¹ * g) ∈ (pPrimeCore 2 K).map K.subtype
      exact (mem_coreActionKernel.mp hkv).2 p (hP.le hp)
    have hrOdd : p⁻¹ * k * p * k⁻¹ ∈ oddIn K := by
      rwa [hr] at hvo
    have hrP : p⁻¹ * k * p * k⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem (P.inv_mem hp) hkP) hp) (P.inv_mem hkP)
    have hrK : p⁻¹ * k * p * k⁻¹ ∈ K := hP.le hrP
    have hjq : jq K ⟨p⁻¹ * k * p * k⁻¹, hrK⟩ = 1 :=
      (mem_oddIn_iff hrK).mp hrOdd
    have hr1 : p⁻¹ * k * p * k⁻¹ = 1 :=
      eq_one_of_jq_eq_one hP.le hP.isPGroup hrP hjq
    have h1 : p⁻¹ * k * p = k := by
      calc p⁻¹ * k * p = p⁻¹ * k * p * k⁻¹ * k := by group
        _ = k := by rw [hr1, one_mul]
    calc k * p = p * (p⁻¹ * k * p) := by group
      _ = p * k := by rw [h1]
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hql, hlsurj, hT⟩ :=
    exists_sylow_standard hK hL hP2
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hql, hlsurj⟩
  have hk4 : ∃ e ∈ q.ker, e * e ≠ 1 := by
    obtain ⟨c, hc, hc2⟩ := hZ
    refine ⟨c, ?_, hc2⟩
    rw [hqker]
    exact hc
  have hq_e_one : q (jq K ⟨k, hkK⟩) = 1 :=
    hQ.q_eq_one_of_central hk4
      ((hT (jq K ⟨k, hkK⟩)).2 ⟨k, hkP, hkK, rfl⟩) fun e' he' => by
        obtain ⟨p, hpP, hpK, rfl⟩ := (hT e').1 he'
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hkcommP p hpP)
  have hecenter : jq K ⟨k, hkK⟩ ∈ center (Jhat K) := by
    rw [← hqker, MonoidHom.mem_ker]
    exact hq_e_one
  have hkZ : k ∈ zStarIn K :=
    (mem_zStarIn_iff hkK).2 hecenter
  have hkCore : k ∈ coreActionKernel K := by
    have hZJ : zStarIn K = K ⊓ coreActionKernel K :=
      CFSG.ComponentClassification.GSThmB.map_fusionZStar_eq K
    rw [hZJ] at hkZ
    exact (mem_inf.mp hkZ).2
  have hgCore : g ∈ coreActionKernel K := by
    have hmul : k * (k⁻¹ * g) ∈ coreActionKernel K := mul_mem hkCore hkv
    rwa [mul_inv_cancel_left] at hmul
  rwa [CFSG.ComponentClassification.Walter86.centralizerSection_pPrimeCoreOf_eq_coreActionKernel K]

end CFSG.GH74.GLS.NT44
