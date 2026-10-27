module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41Defs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure FzCQFacts (t : G) (S : Subgroup G) (x₁ x₂ lam rho : G) : Prop where
  card_K : Nat.card (twoCore t) = 2 ∨ Nat.card (twoCore t) = 4
  K_two : Nat.card (twoCore t) = 2 → twoCore t = zpowers t
  K_four : Nat.card (twoCore t) = 4 →
    ∃ q : G, twoCore t = zpowers q ∧ orderOf q = 4 ∧ q ^ 2 = t
  card_W : Nat.card (ctxW t x₁ x₂) = 16 * Nat.card (twoCore t)
  not_conj_z : ∀ g : G, g * t * g⁻¹ ≠ (x₁ * x₂) ^ 2
  S_le_N2 : S ≤ fzN2 t x₁ x₂
  V_isFzT2 : IsFzT2 t x₁ x₂ S (l41V S t x₁ x₂)
  card_V : Nat.card (l41V S t x₁ x₂) = 8 * Nat.card (ctxW t x₁ x₂)
  W_le_R : ctxW t x₁ x₂ ≤ fzR t x₁ x₂
  card_R : Nat.card (fzR t x₁ x₂) = 4 * Nat.card (ctxW t x₁ x₂)
  R_le_V : fzR t x₁ x₂ ≤ l41V S t x₁ x₂
  V_eq : l41V S t x₁ x₂ = fzR t x₁ x₂ ⊔ zpowers lam
  lam_not_mem_R : lam ∉ fzR t x₁ x₂
  Q_eq : fzQ t x₁ x₂ rho = fzR t x₁ x₂
  R_eq_PK : fzR t x₁ x₂ = fzP t x₁ x₂ rho ⊔ twoCore t
  cent_R_rho : fzR t x₁ x₂ ⊓ centralizer ({rho} : Set G) = twoCore t
  rho_norm_R : ∀ x ∈ fzR t x₁ x₂, rho * x * rho⁻¹ ∈ fzR t x₁ x₂
  lam_norm_R : ∀ x ∈ fzR t x₁ x₂, lam * x * lam⁻¹ ∈ fzR t x₁ x₂
  rho_norm_P : ∀ x ∈ fzP t x₁ x₂ rho, rho * x * rho⁻¹ ∈ fzP t x₁ x₂ rho
  lam_norm_P : ∀ x ∈ fzP t x₁ x₂ rho, lam * x * lam⁻¹ ∈ fzP t x₁ x₂ rho
  P_normal_R : ∀ r ∈ fzR t x₁ x₂, ∀ x ∈ fzP t x₁ x₂ rho, r * x * r⁻¹ ∈ fzP t x₁ x₂ rho
  R_act_t : ∀ r ∈ fzR t x₁ x₂, ∃ f ∈ fourGrp x₁ x₂, r * t * r⁻¹ = t * f
  R_orbit_t : ∀ f ∈ fourGrp x₁ x₂, ∃ r ∈ fzR t x₁ x₂, r * t * r⁻¹ = t * f
  cent_R_t : fzR t x₁ x₂ ⊓ invCent t = ctxW t x₁ x₂
  R_cent_fourGrp : ∀ r ∈ fzR t x₁ x₂, ∀ f ∈ fourGrp x₁ x₂, r * f = f * r
  R_sq_mem_W : ∀ r ∈ fzR t x₁ x₂, r * r ∈ ctxW t x₁ x₂
  R_comm_le_W : ⁅fzR t x₁ x₂, fzR t x₁ x₂⁆ ≤ ctxW t x₁ x₂
  inf_P_K_of_not_mem : t ∉ fzP t x₁ x₂ rho → fzP t x₁ x₂ rho ⊓ twoCore t = ⊥
  card_P_of_not_mem : t ∉ fzP t x₁ x₂ rho →
    Nat.card (fzP t x₁ x₂ rho) * Nat.card (twoCore t) = Nat.card (fzR t x₁ x₂)
  P_fpf_of_not_mem : t ∉ fzP t x₁ x₂ rho →
    ∀ x ∈ fzP t x₁ x₂ rho, rho * x * rho⁻¹ = x → x = 1

end CFSG.OddStandard.SmallF3.FritzII
