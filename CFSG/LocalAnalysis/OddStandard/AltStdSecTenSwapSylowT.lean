module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapTgrp
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapTable
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapFour
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapNoConj
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapThompson

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G}

private theorem exists_conj_iota_τ₀_eq (hC : CentData z ι) {g : G}
    (hg : g ∈ centralizer ({z} : Set G)) :
    ∃ σ : Perm (Fin 10), g * ι τ₀ * g⁻¹ = ι (σ * τ₀ * σ⁻¹) := by
  obtain ⟨σ, hgσ | hgσ⟩ := hC.cases g hg
  · exact ⟨σ, by
      rw [hgσ, show ι σ * ι τ₀ * (ι σ)⁻¹ = ι (σ * τ₀ * σ⁻¹) from by
        rw [map_mul, map_mul, map_inv]]⟩
  · refine ⟨σ, ?_⟩
    have hzτ : z * ι τ₀ * z⁻¹ = ι τ₀ := by rw [hC.comm τ₀]; group
    rw [hgσ]
    calc (z * ι σ) * ι τ₀ * (z * ι σ)⁻¹
        = (ι σ * z) * ι τ₀ * (ι σ * z)⁻¹ := by rw [hC.comm σ]
      _ = ι σ * (z * ι τ₀ * z⁻¹) * (ι σ)⁻¹ := by group
      _ = ι σ * ι τ₀ * (ι σ)⁻¹ := by rw [hzτ]
      _ = ι (σ * τ₀ * σ⁻¹) := by rw [map_mul, map_mul, map_inv]

private theorem commute_of_mem_normalizer_Tgrp (hC : CentData z ι) (hN : NoSwapConj z ι) {x₁ : G}
    {π₁ : ↥(centralizer ({x₁} : Set G)) →* Perm (Fin 10)} (hOS₁ : OneSided z ι x₁ π₁)
    {κ₁ : ↥(centralizer ({x₁} : Set G)) →* ℤˣ} (hκ₁ : Retraction z x₁ κ₁)
    {ι' : Perm (Fin 10) →* G} (h1 : ∀ σ, sign σ = 1 → ι' σ = ι σ)
    (h2 : ∀ σ, sign σ = -1 → ι' σ = z * ι σ) {x₂ : G}
    {π₂ : ↥(centralizer ({x₂} : Set G)) →* Perm (Fin 10)} (hOS₂ : OneSided z ι' x₂ π₂)
    {κ₂ : ↥(centralizer ({x₂} : Set G)) →* ℤˣ} (hκ₂ : Retraction z x₂ κ₂)
    {Q : Subgroup (Perm (Fin 10))} (hQ : GoodQ Q) :
    normalizer (Tgrp z ι Q : Set G) ≤
      centralizer ({z} : Set G) ⊓ centralizer ({ι ρ₄} : Set G) := by
  intro g hg
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := pairOrder_table hC hN hOS₁ hκ₁ h1 h2 hOS₂ hκ₂
  have hρ4sq : ρ₄ * ρ₄ = 1 := by rw [← liftS8_ρ₄', ← map_mul, ρ₄'_mul_self, map_one]
  have ha : z * z = 1 := hC.mul_self
  have hb : ι τ₀ * ι τ₀ = 1 := by rw [← map_mul, τ₀_mul_self, map_one]
  have hc : ι ρ₄ * ι ρ₄ = 1 := by rw [← map_mul, hρ4sq, map_one]
  have hab : z * ι τ₀ = ι τ₀ * z := hC.comm τ₀
  have hac : z * ι ρ₄ = ι ρ₄ * z := hC.comm ρ₄
  have hbc : ι τ₀ * ι ρ₄ = ι ρ₄ * ι τ₀ := by
    rw [← map_mul, ← map_mul, ← liftS8_ρ₄']
    exact congrArg ι (liftS8_mul_τ₀ ρ₄').symm
  have ha1 : z ≠ 1 := by
    intro h
    have hz1 : orderOf z = 1 := by rw [h, orderOf_one]
    rw [hC.order] at hz1
    exact absurd hz1 (by decide)
  have hb1 : ι τ₀ ≠ 1 := by
    intro h
    have hτ : τ₀ = 1 := hC.inj (by rw [h, map_one])
    exact absurd hτ (by decide)
  have hc1 : ι ρ₄ ≠ 1 := by
    intro h
    have hρ : ρ₄ = 1 := hC.inj (by rw [h, map_one])
    exact absurd hρ (by decide)
  have hba : ι τ₀ ≠ z := hC.ne_z τ₀
  have hca : ι ρ₄ ≠ z := hC.ne_z ρ₄
  have hcb : ι ρ₄ ≠ ι τ₀ := fun h => by
    have hρτ : ρ₄ = τ₀ := hC.inj h
    exact absurd hρτ (by decide)
  have hcab : ι ρ₄ ≠ z * ι τ₀ := by
    intro h
    have hz : z = ι (ρ₄ * τ₀⁻¹) := by
      have h' : z = ι ρ₄ * (ι τ₀)⁻¹ := by rw [h]; group
      rwa [← map_inv, ← map_mul] at h'
    exact hC.ne_z _ hz.symm
  have hz1 : ∀ g : G, g * z * g⁻¹ ≠ ι τ₀ := by
    intro g hg
    exact not_isConj_z_ι hC hN hOS₁ hκ₁ τ₀ (isConj_iff.2 ⟨g, hg⟩)
  have hz2 : ∀ g : G, g * z * g⁻¹ ≠ z * ι τ₀ := by
    intro g hg
    exact (hN τ₀ isSwap_τ₀).2 (isConj_iff.2 ⟨g, hg⟩)
  have hb' : ∀ g : G, g * z = z * g → g * ι τ₀ * g⁻¹ ≠ z * ι τ₀ := by
    intro g hgz hconj
    obtain ⟨σ, hσ⟩ := exists_conj_iota_τ₀_eq hC (mem_centralizer_singleton_iff.2 hgz)
    have h : ι (σ * τ₀ * σ⁻¹) = z * ι τ₀ := hσ.symm.trans hconj
    have hz : z = ι (σ * τ₀ * σ⁻¹ * τ₀⁻¹) := by
      have h' : z = ι (σ * τ₀ * σ⁻¹) * (ι τ₀)⁻¹ := by rw [h]; group
      rwa [← map_inv, ← map_mul] at h'
    exact hC.ne_z _ hz.symm
  have hrig := commute_of_mem_normalizer_of_pairOrder
    (a := z) (b := ι τ₀) (c := ι ρ₄)
    (F := Fgrp (Tgrp z ι Q))
    (N₁ := N10 1) (N₄ := N10 4) (N₅ := N10 5)
    ha hb hc hab hac hbc ha1 hb1 hba hc1 hca hcb hcab
    (fun p => mem_Fgrp_iff hC hQ)
    N10_one_ne_four N10_one_ne_five N10_four_ne_five
    e1 e2 e3 e4 e5 e6 e7 hz1 hz2 hb'
    (normalizer_le_normalizer_Fgrp (Tgrp z ι Q) hg)
  exact Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 hrig.1,
    mem_centralizer_singleton_iff.2 hrig.2.2⟩

theorem not_two_dvd_index_Tgrp (hC : CentData z ι) (hN : NoSwapConj z ι) {x₁ : G}
    {π₁ : ↥(centralizer ({x₁} : Set G)) →* Perm (Fin 10)} (hOS₁ : OneSided z ι x₁ π₁)
    {κ₁ : ↥(centralizer ({x₁} : Set G)) →* ℤˣ} (hκ₁ : Retraction z x₁ κ₁)
    {ι' : Perm (Fin 10) →* G} (h1 : ∀ σ, sign σ = 1 → ι' σ = ι σ)
    (h2 : ∀ σ, sign σ = -1 → ι' σ = z * ι σ) {x₂ : G}
    {π₂ : ↥(centralizer ({x₂} : Set G)) →* Perm (Fin 10)} (hOS₂ : OneSided z ι' x₂ π₂)
    {κ₂ : ↥(centralizer ({x₂} : Set G)) →* ℤˣ} (hκ₂ : Retraction z x₂ κ₂)
    {Q : Subgroup (Perm (Fin 10))} (hQ : GoodQ Q) : ¬ 2 ∣ (Tgrp z ι Q).index := by
  have hTpg : IsPGroup 2 (Tgrp z ι Q) := Tgrp_isPGroup hC hQ.pgroup
  have hTcard : Nat.card (Tgrp z ι Q) = 2 ^ 9 := by
    rw [Tgrp_card hC Q, hQ.card]
    norm_num
  have hle : normalizer (Tgrp z ι Q : Set G) ≤
      centralizer ({z} : Set G) ⊓ centralizer ({ι ρ₄} : Set G) :=
    commute_of_mem_normalizer_Tgrp hC hN hOS₁ hκ₁ h1 h2 hOS₂ hκ₂ hQ
  have hpair : pairOrder z (ι ρ₄) = N10 4 :=
    (pairOrder_table hC hN hOS₁ hκ₁ h1 h2 hOS₂ hκ₂).2.1
  have hHcard : ¬ 2 ^ (9 + 1) ∣
      Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({ι ρ₄} : Set G)) := by
    change ¬ 2 ^ (9 + 1) ∣ pairOrder z (ι ρ₄)
    rw [hpair, N10_four]
    norm_num
  exact not_two_dvd_index_of_normalizer_le hTpg hle hTcard hHcard

end CFSG.OddStandard.AltStdSec.SwapPattern
