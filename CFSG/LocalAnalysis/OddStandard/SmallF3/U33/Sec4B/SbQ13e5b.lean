module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e4c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0g

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13e_card_B_le (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hC : Q13C t x₁ x₂ lam tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    Nat.card (q13B t tau x₁ x₂ rho om) ≤ 2 ^ 9 := by
  let B : Subgroup G := q13B t tau x₁ x₂ rho om
  let P : Subgroup G := q13P t tau x₁ x₂ rho om
  let f : G := t * lam
  have hBleL : B ≤ q13L t tau x₁ x₂ rho om := inf_le_left
  have hPleB : P ≤ B := (q13d_P_le_E0 h).trans hD.E0_le_B
  have hPnorm : ∀ k ∈ B, ∀ p ∈ P, k * p * k⁻¹ ∈ P := by
    intro k hk p hp
    exact q13d_P_normal_L h hD.A_cent k (hBleL hk) p hp
  have hsq : ∀ k ∈ B, k * k ∈ P := by
    intro k hk
    have hk' : k * k ∈ q13CLP t tau x₁ x₂ rho om := q13e_sq_mem_CLP h hD k hk
    rw [q13e_CLP_eq_P h hB hC hD] at hk'
    exact hk'
  have hf : f * f = 1 := q13c_tlam_sq h
  have hfL : f ∈ q13L t tau x₁ x₂ rho om := q13e_f_mem_L h hD
  have hfB : ∀ k ∈ B, f * k * f⁻¹ ∈ B := by
    intro k hk
    exact hD.B_normal.2 f hfL k hk
  have hfP : ∀ p ∈ P, f * p * f⁻¹ ∈ P := by
    intro p hp
    exact q13d_P_normal_L h hD.A_cent f hfL p hp
  have htB : t ∈ B := hD.E0_le_B (q13d_t_mem_E0 h)
  have hft : f * t * f⁻¹ * t⁻¹ ∈ P := by
    have hcomm : f * t = t * f := q13e_f_t h
    have hft' : f * t * f⁻¹ = t := by rw [hcomm]; group
    rw [hft']
    simpa using P.one_mem
  have hnot : ∀ k ∈ B, (f * k * f⁻¹ * k⁻¹) * t⁻¹ ∉ P := by
    intro k hk hmem
    let p : G := (f * k * f⁻¹ * k⁻¹) * t⁻¹
    have hpP : p ∈ P := hmem
    have hkL : k ∈ q13L t tau x₁ x₂ rho om := hBleL hk
    have hgL : f * k ∈ q13L t tau x₁ x₂ rho om := mul_mem hfL hkL
    have hb2P : k * k ∈ P := hsq k hk
    have hpt : p * t = t * p⁻¹ := by
      have h2 : t * p⁻¹ * t⁻¹ = p := by
        have h3 := hD.t_inv_P p⁻¹ (P.inv_mem hpP)
        simpa using h3
      calc p * t = (t * p⁻¹ * t⁻¹) * t := by rw [h2]
        _ = t * p⁻¹ := by group
    have hgg : (f * k) * (f * k) = t * (p⁻¹ * (k * k)) := by
      have hff : f⁻¹ = f := q13e_f_inv h
      calc (f * k) * (f * k)
          = (f * k * f⁻¹ * k⁻¹) * (k * k) := by rw [hff]; group
        _ = (p * t) * (k * k) := by
            congr 1
            show f * k * f⁻¹ * k⁻¹ = p * t
            dsimp [p]
            group
        _ = t * (p⁻¹ * (k * k)) := by rw [hpt]; group
    exact q13e_no_sq h hD (f * k) hgL (p⁻¹ * (k * k))
      (P.mul_mem (P.inv_mem hpP) hb2P) hgg
  have hmain := q13e_two_mul_card_mul_le_ncard_fix_sq (K := B) (H := P) (f := f)
    hPleB hPnorm hsq hf hfB hfP htB hft hnot
  have hbound : ({k | k ∈ B ∧ f * k * f⁻¹ * k⁻¹ ∈ P} : Set G).ncard ≤ 2 ^ 8 :=
    q13e_ncard_fix_B h hC hD
  have hPcard : Nat.card P = 2 ^ 6 := q13d_card_P h hD.A_cent
  have hsq2 : ({k | k ∈ B ∧ f * k * f⁻¹ * k⁻¹ ∈ P} : Set G).ncard ^ 2 ≤ (2 ^ 8) ^ 2 :=
    Nat.pow_le_pow_left hbound 2
  have hmain' : 2 * (Nat.card B * 2 ^ 6) ≤ (2 ^ 8) ^ 2 := by
    calc 2 * (Nat.card B * 2 ^ 6) = 2 * (Nat.card B * Nat.card P) := by rw [hPcard]
      _ ≤ _ := le_trans hmain hsq2
  have h' : 2 * (Nat.card B * 64) ≤ 65536 := by
    simpa using hmain'
  have hx : Nat.card B ≤ 512 := by omega
  change Nat.card B ≤ 2 ^ 9
  simpa using hx

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
