module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e7d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13e_B_le_L : q13B t tau x₁ x₂ rho om ≤ q13L t tau x₁ x₂ rho om :=
  inf_le_left

theorem q13e_false (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hC : Q13C t x₁ x₂ lam tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    False := by
  have hHK : q13AN t tau x₁ x₂ rho ≤ q13R t tau x₁ x₂ rho om :=
    (q13e_AN_le_P h).trans (q13e_P_le_R h hD)
  have hHnorm : ∀ k ∈ q13R t tau x₁ x₂ rho om, ∀ a ∈ q13AN t tau x₁ x₂ rho,
      k * a * k⁻¹ ∈ q13AN t tau x₁ x₂ rho := by
    intro k hk a ha
    exact q13e_AN_normal_L h hD k (q13e_B_le_L (q13e_R_le_B hk)) a ha
  have hsq : ∀ k ∈ q13R t tau x₁ x₂ rho om, k * k ∈ q13AN t tau x₁ x₂ rho :=
    q13e_R_sq_mem_AN h hB hC hD
  have hf : (t * lam) * (t * lam) = 1 := q13c_tlam_sq h
  have hfK : ∀ k ∈ q13R t tau x₁ x₂ rho om, (t * lam) * k * (t * lam)⁻¹ ∈
      q13R t tau x₁ x₂ rho om := q13e_f_R h hC hD
  have hfH : ∀ a ∈ q13AN t tau x₁ x₂ rho, (t * lam) * a * (t * lam)⁻¹ ∈
      q13AN t tau x₁ x₂ rho := by
    intro a ha
    exact q13e_AN_normal_L h hD (t * lam) (q13e_f_mem_L h hD) a ha
  let X : Set G := {k | k ∈ q13R t tau x₁ x₂ rho om ∧
    (t * lam) * k * (t * lam)⁻¹ * k⁻¹ ∈ q13AN t tau x₁ x₂ rho}
  have hXeq : X = {k | k ∈ q13R t tau x₁ x₂ rho om ∧
      (t * lam) * k * (t * lam)⁻¹ * k⁻¹ ∈ q13AN t tau x₁ x₂ rho} := rfl
  have hcount : Nat.card (q13R t tau x₁ x₂ rho om) * Nat.card (q13AN t tau x₁ x₂ rho) ≤
      X.ncard ^ 2 :=
    q13e_card_mul_le_ncard_fix_sq hHK hHnorm hsq hf hfK hfH
  rw [q13e_card_R h hB hC hD, q13e_card_AN h] at hcount
  have hcount' : (2 : ℕ) ^ 13 ≤ X.ncard ^ 2 := by
    have hpow : (2 : ℕ) ^ 8 * 2 ^ 5 = 2 ^ 13 := by norm_num
    rwa [hpow] at hcount
  have hgt : 2 ^ 6 < X.ncard := by
    by_contra hle
    rw [not_lt] at hle
    have h2 : X.ncard ^ 2 ≤ (2 ^ 6) ^ 2 := Nat.pow_le_pow_left hle 2
    norm_num at hcount' h2
    omega
  have hcardP : (q13P t tau x₁ x₂ rho om : Set G).ncard = 2 ^ 6 := by
    rw [← Nat.card_coe_set_eq]
    exact q13d_card_P h hD.A_cent
  have hnotsub : ¬ X ⊆ (q13P t tau x₁ x₂ rho om : Set G) := by
    intro hsub
    have hle : X.ncard ≤ (q13P t tau x₁ x₂ rho om : Set G).ncard := Set.ncard_le_ncard hsub
    rw [hcardP] at hle
    omega
  obtain ⟨r, hrX, hrP⟩ := Set.not_subset.mp hnotsub
  rw [hXeq] at hrX
  have hrR : r ∈ q13R t tau x₁ x₂ rho om := hrX.1
  have hrn : (t * lam) * r * (t * lam)⁻¹ * r⁻¹ ∈ q13AN t tau x₁ x₂ rho := hrX.2
  set p : G := r⁻¹ * ((t * lam) * r * (t * lam)⁻¹ * r⁻¹) * r with hp_def
  have hfact : (t * lam) * r * (t * lam)⁻¹ = r * p := by
    rw [hp_def]; group
  have hpAN : p ∈ q13AN t tau x₁ x₂ rho := by
    have hrL : r⁻¹ ∈ q13L t tau x₁ x₂ rho om :=
      (q13L t tau x₁ x₂ rho om).inv_mem (q13e_B_le_L (q13e_R_le_B hrR))
    have hconj := q13e_AN_normal_L h hD r⁻¹ hrL
      ((t * lam) * r * (t * lam)⁻¹ * r⁻¹) hrn
    simpa [hp_def] using hconj
  have hpZ : p * ((t * lam) * p * (t * lam)⁻¹) = 1 := q13e_cocycle h hfact
  have hpH1 : p ∈ q13H1 t tau x₁ x₂ lam rho := q13e_Z1_AN h p hpAN hpZ
  have hrB : r ∈ q13B t tau x₁ x₂ rho om := q13e_R_le_B hrR
  have hrE0 : r ∈ q13E0 t tau x₁ x₂ rho om := q13e_class_one h hC hD hrB hpH1 hfact
  exact hrP (q13e_R_inf_E0 h hD r hrR hrE0)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
