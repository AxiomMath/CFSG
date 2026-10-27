module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapPair
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapTwist
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapReps

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G}

private theorem liftS8_mul_self_of_mul_self {ρ : Perm (Fin 8)} (hρ : ρ * ρ = 1) :
    liftS8 ρ * liftS8 ρ = 1 := by
  rw [← map_mul, hρ, map_one]

theorem CentData.of_twist (hC : CentData z ι) {ι' : Perm (Fin 10) →* G}
    (h1 : ∀ σ, sign σ = 1 → ι' σ = ι σ) (h2 : ∀ σ, sign σ = -1 → ι' σ = z * ι σ) :
    CentData z ι' := by
  obtain ⟨ι'', hC'', h1'', h2''⟩ := hC.exists_twist
  have heq : ι' = ι'' := by
    ext σ
    rcases Int.units_eq_one_or (sign σ) with hs | hs
    · rw [h1 σ hs, h1'' σ hs]
    · rw [h2 σ hs, h2'' σ hs]
  rw [heq]
  exact hC''

theorem pairOrder_z_ι (hC : CentData z ι) {σ : Perm (Fin 10)} (hσ : σ * σ = 1) :
    pairOrder z (ι σ) = N10 (Multiset.card σ.cycleType) := by
  rw [pairOrder, hC.card_inf_centralizer σ, two_mul_card_centralizer_perm_ten hσ]

theorem pairOrder_x_ι_liftS8 (hC : CentData z ι) (hN : NoSwapConj z ι) {x : G}
    {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)} (hOS : OneSided z ι x π)
    {κ : ↥(centralizer ({x} : Set G)) →* ℤˣ} (hκ : Retraction z x κ) {ρ : Perm (Fin 8)}
    (hρ : ρ * ρ = 1) :
    pairOrder x (ι (liftS8 ρ)) =
        N10 (Multiset.card ρ.cycleType + (if Odd (Multiset.card ρ.cycleType) then 1 else 0)) ∧
      pairOrder x (z * ι (liftS8 ρ)) =
        N10 (Multiset.card ρ.cycleType + (if Odd (Multiset.card ρ.cycleType) then 0 else 1)) := by
  have hx2 : x * x = 1 := by
    rw [hOS.eq, ← map_mul, τ₀_mul_self, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    have h' : x = ι 1 := by rw [h, map_one]
    have h'' : τ₀ = 1 := hC.inj (by rw [← hOS.eq, h'])
    exact absurd h'' (by decide)
  have hρx : ι (liftS8 ρ) ∈ centralizer ({x} : Set G) := by
    rw [hOS.eq]
    exact ι_liftS8_mem_centralizer ι ρ
  have hzρ : z * ι (liftS8 ρ) ∈ centralizer ({x} : Set G) :=
    z_mul_liftS8_mem_centralizer hC hOS ρ
  have hf1 : (⟨ι (liftS8 ρ), hρx⟩ : ↥(centralizer ({x} : Set G))) *
      ⟨ι (liftS8 ρ), hρx⟩ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    show ι (liftS8 ρ) * ι (liftS8 ρ) = 1
    calc ι (liftS8 ρ) * ι (liftS8 ρ) = ι (liftS8 ρ * liftS8 ρ) := by rw [map_mul]
      _ = ι 1 := by rw [liftS8_mul_self_of_mul_self hρ]
      _ = 1 := map_one ι
  have hf2 : (⟨z * ι (liftS8 ρ), hzρ⟩ : ↥(centralizer ({x} : Set G))) *
      ⟨z * ι (liftS8 ρ), hzρ⟩ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    show (z * ι (liftS8 ρ)) * (z * ι (liftS8 ρ)) = 1
    calc (z * ι (liftS8 ρ)) * (z * ι (liftS8 ρ))
        = z * (ι (liftS8 ρ) * z) * ι (liftS8 ρ) := by group
      _ = z * (z * ι (liftS8 ρ)) * ι (liftS8 ρ) := by rw [hC.comm (liftS8 ρ)]
      _ = (z * z) * (ι (liftS8 ρ) * ι (liftS8 ρ)) := by group
      _ = ι (liftS8 ρ) * ι (liftS8 ρ) := by rw [hC.mul_self, one_mul]
      _ = ι (liftS8 ρ * liftS8 ρ) := by rw [map_mul]
      _ = 1 := by rw [liftS8_mul_self_of_mul_self hρ, map_one]
  have hπ1 : π ⟨ι (liftS8 ρ), hρx⟩ * π ⟨ι (liftS8 ρ), hρx⟩ = 1 := by
    rw [← map_mul, hf1, map_one]
  have hπ2 : π ⟨z * ι (liftS8 ρ), hzρ⟩ * π ⟨z * ι (liftS8 ρ), hzρ⟩ = 1 := by
    rw [← map_mul, hf2, map_one]
  obtain ⟨-, hcycle⟩ := twist_facts hC hN hOS hκ ρ hρx hzρ
  obtain ⟨hc1, hc2⟩ := hcycle hρ
  have hbase1 := SymSec.card_inf_centralizer hOS.sec hκ.self hx2 hx1
    (⟨ι (liftS8 ρ), hρx⟩ : ↥(centralizer ({x} : Set G)))
  have hbase2 := SymSec.card_inf_centralizer hOS.sec hκ.self hx2 hx1
    (⟨z * ι (liftS8 ρ), hzρ⟩ : ↥(centralizer ({x} : Set G)))
  have hpair1 : pairOrder x (ι (liftS8 ρ)) =
      2 * Nat.card ↥(centralizer ({π ⟨ι (liftS8 ρ), hρx⟩} : Set (Perm (Fin 10)))) := by
    rw [pairOrder]
    exact hbase1
  have hpair2 : pairOrder x (z * ι (liftS8 ρ)) =
      2 * Nat.card ↥(centralizer ({π ⟨z * ι (liftS8 ρ), hzρ⟩} : Set (Perm (Fin 10)))) := by
    rw [pairOrder]
    exact hbase2
  exact ⟨by rw [hpair1, two_mul_card_centralizer_perm_ten hπ1, hc1],
    by rw [hpair2, two_mul_card_centralizer_perm_ten hπ2, hc2]⟩

theorem pairOrder_table (hC : CentData z ι) (hN : NoSwapConj z ι) {x₁ : G}
    {π₁ : ↥(centralizer ({x₁} : Set G)) →* Perm (Fin 10)} (hOS₁ : OneSided z ι x₁ π₁)
    {κ₁ : ↥(centralizer ({x₁} : Set G)) →* ℤˣ} (hκ₁ : Retraction z x₁ κ₁)
    {ι' : Perm (Fin 10) →* G} (h1 : ∀ σ, sign σ = 1 → ι' σ = ι σ)
    (h2 : ∀ σ, sign σ = -1 → ι' σ = z * ι σ) {x₂ : G}
    {π₂ : ↥(centralizer ({x₂} : Set G)) →* Perm (Fin 10)} (hOS₂ : OneSided z ι' x₂ π₂)
    {κ₂ : ↥(centralizer ({x₂} : Set G)) →* ℤˣ} (hκ₂ : Retraction z x₂ κ₂) :
    pairOrder z (ι τ₀) = N10 1 ∧ pairOrder z (ι ρ₄) = N10 4 ∧
      pairOrder z (ι τ₀ * ι ρ₄) = N10 5 ∧ pairOrder (ι τ₀) (ι ρ₄) = N10 4 ∧
      pairOrder (ι τ₀) (z * ι ρ₄) = N10 5 ∧ pairOrder (z * ι τ₀) (ι ρ₄) = N10 4 ∧
      pairOrder (z * ι τ₀) (z * ι ρ₄) = N10 5 := by
  have hρ₄sq : ρ₄ * ρ₄ = 1 := by
    rw [← liftS8_ρ₄', ← map_mul, ρ₄'_mul_self, map_one]
  have hcardρ₄ : Multiset.card ρ₄.cycleType = 4 := by
    rw [← liftS8_ρ₄', cycleType_liftS8, card_cycleType_ρ₄']
  have hsignρ₄ : sign ρ₄ = 1 := by
    rw [← liftS8_ρ₄', sign_liftS8, sign_ρ₄']
  have e1 : pairOrder z (ι τ₀) = N10 1 := by
    rw [pairOrder_z_ι hC τ₀_mul_self, card_cycleType_of_isSwap isSwap_τ₀]
  have e2 : pairOrder z (ι ρ₄) = N10 4 := by
    rw [pairOrder_z_ι hC hρ₄sq, hcardρ₄]
  have e3 : pairOrder z (ι τ₀ * ι ρ₄) = N10 5 := by
    rw [← map_mul, pairOrder_z_ι hC τ₀_mul_ρ₄_mul_self, card_cycleType_τ₀_mul_ρ₄]
  obtain ⟨h4', h5'⟩ := pairOrder_x_ι_liftS8 hC hN hOS₁ hκ₁ (ρ := ρ₄') ρ₄'_mul_self
  rw [card_cycleType_ρ₄'] at h4' h5'
  norm_num at h4' h5'
  have h4 : pairOrder (ι τ₀) (ι ρ₄) = N10 4 := by
    rw [← hOS₁.eq, ← liftS8_ρ₄']
    exact h4'
  have h5 : pairOrder (ι τ₀) (z * ι ρ₄) = N10 5 := by
    rw [← hOS₁.eq, ← liftS8_ρ₄']
    exact h5'
  have hC' : CentData z ι' := CentData.of_twist hC h1 h2
  have hN' : NoSwapConj z ι' := NoSwapConj.twist hC hN h1 h2
  have hι'ρ₄ : ι' ρ₄ = ι ρ₄ := h1 ρ₄ hsignρ₄
  have hx2eq : x₂ = z * ι τ₀ := hOS₂.eq.trans (h2 τ₀ sign_τ₀)
  obtain ⟨h6', h7'⟩ := pairOrder_x_ι_liftS8 hC' hN' hOS₂ hκ₂ (ρ := ρ₄') ρ₄'_mul_self
  rw [card_cycleType_ρ₄'] at h6' h7'
  norm_num at h6' h7'
  rw [liftS8_ρ₄', hι'ρ₄, hx2eq] at h6' h7'
  exact ⟨e1, e2, e3, h4, h5, h6', h7'⟩

end CFSG.OddStandard.AltStdSec.SwapPattern
