module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e4b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e4c0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e1c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e4a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13e_card_CLP_mul_le_ncard_fix_sq (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau) (hD : Q13D t x₁ x₂ lam rho tau om) :
    Nat.card (q13CLP t tau x₁ x₂ rho om) * Nat.card (q13P t tau x₁ x₂ rho om) ≤
      ({k | k ∈ q13CLP t tau x₁ x₂ rho om ∧
        (t * lam) * k * (t * lam)⁻¹ * k⁻¹ ∈ q13P t tau x₁ x₂ rho om} : Set G).ncard ^ 2 := by
  let K : Subgroup G := q13CLP t tau x₁ x₂ rho om
  let P : Subgroup G := q13P t tau x₁ x₂ rho om
  let f : G := t * lam
  have hPK : P ≤ K := q13e_P_le_CLP h hD
  have hfL : f ∈ q13L t tau x₁ x₂ rho om := q13e_f_mem_L h hD
  have hf_sq : f * f = 1 := q13c_tlam_sq h
  have hHnorm : ∀ k ∈ K, ∀ p ∈ P, k * p * k⁻¹ ∈ P := by
    intro k hk p hp
    exact q13d_P_normal_L h hD.A_cent k (Subgroup.mem_inf.mp hk).1 p hp
  have hfK : ∀ k ∈ K, f * k * f⁻¹ ∈ K := by
    intro k hk
    exact q13e_CLP_normal_L h hD f hfL k hk
  have hfH : ∀ p ∈ P, f * p * f⁻¹ ∈ P := by
    intro p hp
    exact q13d_P_normal_L h hD.A_cent f hfL p hp
  have hsq : ∀ k ∈ K, k * k ∈ P := fun k hk => q13e_CLP_sq_mem_P h hB hD k hk
  exact q13e_card_mul_le_ncard_fix_sq hPK hHnorm hsq hf_sq hfK hfH

theorem q13e_K_eq_P (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hC : Q13C t x₁ x₂ lam tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ k ∈ q13L t tau x₁ x₂ rho om, (∀ p ∈ q13P t tau x₁ x₂ rho om,
      k * p = p * k) → k ∈ q13P t tau x₁ x₂ rho om := by
  let K : Subgroup G := q13CLP t tau x₁ x₂ rho om
  let P : Subgroup G := q13P t tau x₁ x₂ rho om
  let f : G := t * lam
  let Fix : Set G := {k | k ∈ K ∧ f * k * f⁻¹ * k⁻¹ ∈ P}
  have hPK : P ≤ K := q13e_P_le_CLP h hD
  have hcount : Nat.card K * Nat.card P ≤ Fix.ncard ^ 2 :=
    q13e_card_CLP_mul_le_ncard_fix_sq h hB hD
  have hPcard : Nat.card P = 2 ^ 6 := q13d_card_P h hD.A_cent
  have hfix7 : Fix.ncard ≤ 2 ^ 7 := q13e_ncard_fix_CLP h hC hD
  have hK8 : Nat.card K ≤ 2 ^ 8 := by
    have h1 : Nat.card K * 2 ^ 6 ≤ 2 ^ 14 := by
      calc Nat.card K * 2 ^ 6 = Nat.card K * Nat.card P := by rw [hPcard]
        _ ≤ Fix.ncard ^ 2 := hcount
        _ ≤ (2 ^ 7) ^ 2 := Nat.pow_le_pow_left hfix7 2
        _ = 2 ^ 14 := by norm_num
    have h2 : Nat.card K * 2 ^ 6 ≤ 2 ^ 8 * 2 ^ 6 := by
      calc Nat.card K * 2 ^ 6 ≤ 2 ^ 14 := h1
        _ = 2 ^ 8 * 2 ^ 6 := by norm_num
    exact Nat.le_of_mul_le_mul_right h2 (by norm_num)
  have hno : ¬ ∃ k ∈ K, ⁅t, k⁆ ∉ q13AN t tau x₁ x₂ rho := by
    rintro ⟨k, hkK, hkA⟩
    have h9 : Nat.card K = 2 ^ 9 := q13e_card_CLP_of_not_AN h hB hD ⟨k, hkK, hkA⟩
    rw [h9] at hK8
    norm_num at hK8
  have hfix_sub : Fix ⊆ (P : Set G) := by
    intro k hk
    have hkAN : ⁅t, k⁆ ∈ q13AN t tau x₁ x₂ rho := by
      by_contra hkA
      exact hno ⟨k, hk.1, hkA⟩
    exact q13e_E3 h hC hD k hk.1 hk.2 hkAN
  have hfix6 : Fix.ncard ≤ 2 ^ 6 := by
    calc Fix.ncard ≤ (P : Set G).ncard := Set.ncard_le_ncard hfix_sub
      _ = Nat.card P := (Nat.card_coe_set_eq (P : Set G)).symm
      _ = 2 ^ 6 := hPcard
  have hK6 : Nat.card K ≤ 2 ^ 6 := by
    have h1 : Nat.card K * 2 ^ 6 ≤ 2 ^ 12 := by
      calc Nat.card K * 2 ^ 6 = Nat.card K * Nat.card P := by rw [hPcard]
        _ ≤ Fix.ncard ^ 2 := hcount
        _ ≤ (2 ^ 6) ^ 2 := Nat.pow_le_pow_left hfix6 2
        _ = 2 ^ 12 := by norm_num
    have h2 : Nat.card K * 2 ^ 6 ≤ 2 ^ 6 * 2 ^ 6 := by
      calc Nat.card K * 2 ^ 6 ≤ 2 ^ 12 := h1
        _ = 2 ^ 6 * 2 ^ 6 := by norm_num
    exact Nat.le_of_mul_le_mul_right h2 (by norm_num)
  have hKP : K = P := by
    have hcard : Nat.card K ≤ Nat.card P := by rw [hPcard]; exact hK6
    exact (Subgroup.eq_of_le_of_card_ge hPK hcard).symm
  intro k hkL hkcomm
  have hkK : k ∈ K := by
    change k ∈ q13CLP t tau x₁ x₂ rho om
    rw [q13CLP, Subgroup.mem_inf]
    exact ⟨hkL, Subgroup.mem_centralizer_iff.mpr (fun p hp => (hkcomm p hp).symm)⟩
  show k ∈ P
  rw [← hKP]
  exact hkK

theorem q13e_CLP_eq_P (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hC : Q13C t x₁ x₂ lam tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    q13CLP t tau x₁ x₂ rho om = q13P t tau x₁ x₂ rho om := by
  apply le_antisymm
  · intro k hk
    obtain ⟨hkL, hkC⟩ := Subgroup.mem_inf.mp hk
    exact q13e_K_eq_P h hB hC hD k hkL
      (fun p hp => (Subgroup.mem_centralizer_iff.mp hkC p hp).symm)
  · exact q13e_P_le_CLP h hD

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
