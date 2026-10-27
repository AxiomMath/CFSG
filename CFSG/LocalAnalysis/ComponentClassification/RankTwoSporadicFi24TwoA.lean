module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24Census
public import CFSG.Sporadic.FischerOddCore.Fi24TJComp
public import CFSG.Sporadic.Fi24.EdgeSwapCert
public import CFSG.Sporadic.Fi22.InvFix
public import Certificates.Certificate1000
public import Certificates.Certificate1001
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1004
public import Certificates.Certificate1005
public import Certificates.Certificate1006
public import Certificates.Certificate1007
public import Certificates.Certificate1009
public import Certificates.Certificate1010
public import Certificates.Certificate1011
public import Certificates.Certificate1012
public import Certificates.Certificate1013
public import Certificates.Certificate1016
public import Certificates.Certificate1017
public import Certificates.Certificate1018
public import Certificates.Certificate1019

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

open Subgroup CFSG.Fischer CFSG.Blueprint.Fischer
open CFSG.Sporadic.Fi24 (R J tR jR JR xb D24 CE)

local notation "LEdge" => CFSG.Sporadic.Fi24.LE

theorem mul_comm_mul_of_comm {G : Type*} [Group G] {c t u : G} (hcu : c * u = u * c)
    (htu : t * u = u * t) : c * t * u = u * (c * t) := by
  rw [mul_assoc, htu, ← mul_assoc, hcu, mul_assoc]

theorem conj_mul_eq_of_conj {G : Type*} [Group G] {c t w : G} (hc : c * w * c⁻¹ = w)
    (ht : t * w * t⁻¹ = w) : c * t * w * (c * t)⁻¹ = w := by
  rw [mul_inv_rev, show c * t * w * (t⁻¹ * c⁻¹) = c * (t * w * t⁻¹) * c⁻¹ by group, ht, hc]

theorem twoACentralizer
    : TwoACentralizer := by
  intro c _ hc
  have hcomm : ∀ ℓ ∈ LEdge, ℓ * c = c * ℓ := fun ℓ hℓ => mem_centralizer_iff.1 hc ℓ hℓ
  have hxt : xb * tR = tR * xb := CFSG.Sporadic.Fi24.tR_xb_comm.symm
  have htxL : tR * xb ∈ LEdge := by
    refine mem_inf.2 ⟨CFSG.Sporadic.Fi24.tR_mul_xb_mem_CE, mem_centralizer_singleton_iff.2 ?_⟩
    rw [mul_assoc, hxt]
  have hct : c * (tR * xb) = tR * xb * c := (hcomm _ htxL).symm
  obtain ⟨ψ, hψc, hψt⟩ := edgeLocal_of_localPoints CFSG.Sporadic.Fi24.pair_R
    CFSG.Sporadic.Fi23.pair_J CFSG.Sporadic.Fi22.pair_D CFSG.Sporadic.Fi24.localPoints_D24
    (CFSG.Sporadic.Fi23.localPoints_D23 CFSG.Fischer.polarFacts)
    ⟨tR, CFSG.Sporadic.Fi24.tR_mem_D24⟩ ⟨xb, CFSG.Sporadic.Fi24.xb_mem_D24⟩
    CFSG.Sporadic.Fi24.tR_ne_xb CFSG.Sporadic.Fi24.tR_xb_comm
  have hCE : CE ≤ centralizer ({tR * xb} : Set R) := inf_le_left
  have hrange := range_edgeHomL CFSG.Sporadic.Fi24.pair_R CFSG.Sporadic.Fi22.pair_D
    CFSG.Sporadic.Fi24.tR_mem_D24 CFSG.Sporadic.Fi24.xb_mem_D24 CFSG.Sporadic.Fi24.tR_ne_xb
    CFSG.Sporadic.Fi24.tR_xb_comm ψ hψc hψt CFSG.Sporadic.Fi22.center_eq_bot
    CFSG.Sporadic.Fi22.index_innerTau_range hCE CFSG.Sporadic.Fi24.commutator_LE
    (by rw [CFSG.Sporadic.Fi22.card_tauGroup]; exact CFSG.Sporadic.Fi24.card_LE)
    (fun ℓ hℓ h => CFSG.Sporadic.Fi24.eq_of_mem_LE_centralizes hℓ h)
  set ρ := edgeHom CFSG.Sporadic.Fi24.pair_R CFSG.Sporadic.Fi22.pair_D
    CFSG.Sporadic.Fi24.tR_mem_D24 CFSG.Sporadic.Fi24.xb_mem_D24 CFSG.Sporadic.Fi24.tR_ne_xb
    CFSG.Sporadic.Fi24.tR_xb_comm ψ hψc hψt CFSG.Sporadic.Fi22.center_eq_bot with hρdef
  have hρone : ∀ g : ↥(centralizer ({tR * xb} : Set R)), ρ g = 1 ↔
      ∀ w ∈ LocalClass D24 tR ∩ LocalClass D24 xb, (g : R) * w * (g : R)⁻¹ = w :=
    fun g => edgeHom_eq_one_iff CFSG.Sporadic.Fi24.pair_R CFSG.Sporadic.Fi22.pair_D
      CFSG.Sporadic.Fi24.tR_mem_D24 CFSG.Sporadic.Fi24.xb_mem_D24 CFSG.Sporadic.Fi24.tR_ne_xb
      CFSG.Sporadic.Fi24.tR_xb_comm ψ hψc hψt CFSG.Sporadic.Fi22.center_eq_bot g
  have hρeq : ∀ g₁ g₂ : ↥(centralizer ({tR * xb} : Set R)),
      (∀ w ∈ LocalClass D24 tR ∩ LocalClass D24 xb,
        (g₁ : R) * w * (g₁ : R)⁻¹ = (g₂ : R) * w * (g₂ : R)⁻¹) → ρ g₁ = ρ g₂ := by
    intro g₁ g₂ h
    have h1 : ρ (g₂⁻¹ * g₁) = 1 := by
      rw [hρone]
      intro w hw
      rw [coe_mul, coe_inv, mul_inv_rev, inv_inv]
      calc (g₂ : R)⁻¹ * g₁ * w * ((g₁ : R)⁻¹ * g₂) =
          (g₂ : R)⁻¹ * ((g₁ : R) * w * (g₁ : R)⁻¹) * g₂ := by group
        _ = w := by rw [h w hw]; group
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  let cC : ↥(centralizer ({tR * xb} : Set R)) := ⟨c, mem_centralizer_singleton_iff.2 hct⟩
  have hρc : ρ cC = 1 := by
    apply eq_one_of_commute_innerTau CFSG.Sporadic.Fi22.pair_D CFSG.Sporadic.Fi22.center_eq_bot
    intro x
    obtain ⟨ℓ, hℓ⟩ : innerTau CFSG.Sporadic.Fi22.pair_D (x : CFSG.Sporadic.Fi22.J) ∈
        (edgeHomL CFSG.Sporadic.Fi24.pair_R CFSG.Sporadic.Fi22.pair_D
          CFSG.Sporadic.Fi24.tR_mem_D24 CFSG.Sporadic.Fi24.xb_mem_D24 CFSG.Sporadic.Fi24.tR_ne_xb
          CFSG.Sporadic.Fi24.tR_xb_comm ψ hψc hψt CFSG.Sporadic.Fi22.center_eq_bot hCE).range := by
      rw [hrange]
      exact ⟨_, rfl⟩
    rw [← hℓ]
    have hmul : cC * inclusion (inf_le_left.trans hCE) ℓ =
        inclusion (inf_le_left.trans hCE) ℓ * cC := by
      apply Subtype.ext
      rw [coe_mul, coe_mul, coe_inclusion]
      exact (hcomm ℓ ℓ.2).symm
    show ρ cC * ρ (inclusion (inf_le_left.trans hCE) ℓ) =
      ρ (inclusion (inf_le_left.trans hCE) ℓ) * ρ cC
    rw [← map_mul, ← map_mul, hmul]
  have hcW := (hρone cC).1 hρc
  have hmemL : ∀ g : J, jR g * (tR * xb) = tR * xb * jR g → jR g * tR = tR * jR g →
      jR g ∈ LEdge := fun g h1 h2 =>
    mem_inf.2 ⟨mem_inf.2 ⟨mem_centralizer_singleton_iff.2 h1, CFSG.Sporadic.Fi24.jR_mem_JR g⟩,
      mem_centralizer_singleton_iff.2 h2⟩
  have htW : ∀ w ∈ LocalClass D24 tR ∩ LocalClass D24 xb, tR * w * tR⁻¹ = w := by
    intro w hw
    rw [← hw.1.2.2, mul_inv_cancel_right]
  have httx : tR * (tR * xb) = tR * xb * tR := by rw [mul_assoc, hxt]
  rcases conj_eq_or_of_commute_mul CFSG.Sporadic.Fi24.pair_R CFSG.Sporadic.Fi24.tR_mem_D24
      CFSG.Sporadic.Fi24.xb_mem_D24 CFSG.Sporadic.Fi24.tR_ne_xb CFSG.Sporadic.Fi24.tR_xb_comm
      CFSG.Sporadic.FischerOddCore.fi24_hW hct with ⟨h1, -⟩ | ⟨h1, h2⟩
  ·
    have hctR := mul_inv_eq_iff_eq_mul.1 h1
    have hcW' : ∀ w ∈ LocalClass D24 tR ∩ LocalClass D24 xb, c * w * c⁻¹ = w := hcW
    obtain ⟨g, hg | hg⟩ := CFSG.Sporadic.Fi24.eq_jR_or c
    · rw [hg] at hct hctR hcW'
      rcases CFSG.Sporadic.Fi24.eq_of_mem_LE_centralizes (hmemL g hct hctR) hcW' with h | h
      · rw [hg, h]
        exact Or.inl (one_mem _)
      · rw [hg, h]
        exact Or.inl (mem_zpowers _)
    · have hℓ : c * tR = jR g := by rw [hg, mul_assoc, CFSG.Sporadic.Fi24.tR_mul_tR, mul_one]
      have h1' := mul_comm_mul_of_comm (G := R) (c := c) (t := tR) (u := tR * xb) hct httx
      have h2' := mul_comm_mul_of_comm (G := R) (c := c) (t := tR) (u := tR) hctR rfl
      have h3' : ∀ w ∈ LocalClass D24 tR ∩ LocalClass D24 xb, c * tR * w * (c * tR)⁻¹ = w :=
        fun w hw => conj_mul_eq_of_conj (G := R) (c := c) (t := tR) (w := w) (hcW' w hw)
          (htW w hw)
      rw [hℓ] at h1' h2' h3'
      rcases CFSG.Sporadic.Fi24.eq_of_mem_LE_centralizes (hmemL g h1' h2') h3' with h | h
      · rw [hg, h, one_mul]
        exact Or.inr CFSG.Sporadic.Fi24.tR_mem_D24
      · rw [hg, h, mul_assoc, hxt, ← mul_assoc, CFSG.Sporadic.Fi24.tR_mul_tR, one_mul]
        exact Or.inr CFSG.Sporadic.Fi24.xb_mem_D24
  ·
    exfalso
    have he := CFSG.Sporadic.Fi24.edgeSwap_a
    have haCE := CFSG.Sporadic.Fi24.jR_mem_CE he
    have hax := mem_centralizer_singleton_iff.1 (mem_inf.1 haCE).1
    let aC : ↥(centralizer ({tR * xb} : Set R)) :=
      ⟨jR CFSG.Sporadic.Fi24.a, (inf_le_left : CE ≤ _) haCE⟩
    have hd1 : c * jR CFSG.Sporadic.Fi24.a * tR * (c * jR CFSG.Sporadic.Fi24.a)⁻¹ = tR := by
      rw [mul_inv_rev, show c * jR CFSG.Sporadic.Fi24.a * tR * ((jR CFSG.Sporadic.Fi24.a)⁻¹ * c⁻¹) =
        c * (jR CFSG.Sporadic.Fi24.a * tR * (jR CFSG.Sporadic.Fi24.a)⁻¹) * c⁻¹ by group,
        he.swap_tR, h2]
    have hdtR := mul_inv_eq_iff_eq_mul.1 hd1
    have hdu := mul_comm_mul_of_comm (G := R) (c := c) (t := jR CFSG.Sporadic.Fi24.a)
      (u := tR * xb) hct hax
    have hρd : ρ (cC * aC) = ρ aC := by rw [map_mul, hρc, one_mul]
    obtain ⟨ℓ, hℓL, hℓW⟩ : ∃ ℓ ∈ LEdge, ∀ w ∈ LocalClass D24 tR ∩ LocalClass D24 xb,
        c * jR CFSG.Sporadic.Fi24.a * w * (c * jR CFSG.Sporadic.Fi24.a)⁻¹ = ℓ * w * ℓ⁻¹ := by
      obtain ⟨g, hg | hg⟩ := CFSG.Sporadic.Fi24.eq_jR_or (c * jR CFSG.Sporadic.Fi24.a)
      · rw [hg] at hdtR hdu
        refine ⟨jR g, hmemL g hdu hdtR, fun w _ => ?_⟩
        rw [hg]
      · have hℓ : c * jR CFSG.Sporadic.Fi24.a * tR = jR g := by
          rw [hg, mul_assoc, CFSG.Sporadic.Fi24.tR_mul_tR, mul_one]
        have h1' := mul_comm_mul_of_comm (G := R) (c := c * jR CFSG.Sporadic.Fi24.a) (t := tR)
          (u := tR * xb) hdu httx
        have h2' := mul_comm_mul_of_comm (G := R) (c := c * jR CFSG.Sporadic.Fi24.a) (t := tR)
          (u := tR) hdtR rfl
        rw [hℓ] at h1' h2'
        refine ⟨jR g, hmemL g h1' h2', fun w hw => ?_⟩
        rw [hg, show jR g * tR * w * (jR g * tR)⁻¹ = jR g * (tR * w * tR⁻¹) * (jR g)⁻¹ by group,
          htW w hw]
    have hℓC : ℓ ∈ centralizer ({tR * xb} : Set R) := (mem_inf.1 (mem_inf.1 hℓL).1).1
    have hρℓ : ρ (cC * aC) = ρ ⟨ℓ, hℓC⟩ := by
      apply hρeq
      intro w hw
      rw [coe_mul]
      exact hℓW w hw
    rw [hρd] at hρℓ
    have hrng : ρ aC ∈ (innerTau CFSG.Sporadic.Fi22.pair_D).range := by
      rw [hρℓ, ← hrange]
      exact ⟨⟨ℓ, hℓL⟩, rfl⟩
    exact CFSG.Sporadic.Fi24.edgeHom_swap_not_mem he ψ hψc hψt
      CFSG.Sporadic.Fi22.card_fixed_involution_D hrng

end CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
