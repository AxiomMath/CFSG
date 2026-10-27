module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Hyp

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

@[expose] def ctxW {G : Type*} [Group G] (t x₁ x₂ : G) : Subgroup G :=
  twoCore t ⊔ baseGrp x₁ x₂

structure Ctx0 {G : Type} [Group G] [Finite G] (t : G) (L S : Subgroup G)
    (x₁ x₂ lam rho : G) : Prop where
  hyp : Hyp G t L
  le_invCent : S ≤ invCent t
  isPGroup : IsPGroup 2 S
  relIndex_odd : ¬ 2 ∣ S.relIndex (invCent t)
  wreath : WreathRel x₁ x₂ lam
  inf_eq : S ⊓ L = wreathGrp x₁ x₂ lam
  inf_PL : S ⊓ (twoCore t ⊔ L) = twoCore t ⊔ wreathGrp x₁ x₂ lam
  abelian_W : IsMulCommutative (ctxW t x₁ x₂)
  J0_eq : CFSG.ambientMaxCardThompson (twoCore t ⊔ wreathGrp x₁ x₂ lam) = ctxW t x₁ x₂
  PT_eq : twoCore t ⊔ wreathGrp x₁ x₂ lam = ctxW t x₁ x₂ ⊔ zpowers lam
  rho_mem : rho ∈ L
  rho_normalizes : rho ∈ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G)
  ord_rho : orderOf rho = 3
  lam_rho : lam * rho * lam⁻¹ = rho⁻¹
  cent_rho : ctxW t x₁ x₂ ⊓ centralizer ({rho} : Set G) = twoCore t
  comm_rho : ⁅ctxW t x₁ x₂, zpowers rho⁆ = baseGrp x₁ x₂
  invol_L : ∀ g ∈ L, g * g = 1 → g ≠ 1 → ∃ c ∈ L, c * (x₁ * x₂) ^ 2 * c⁻¹ = g
  invol_PL : ∀ g ∈ twoCore t ⊔ L, g * g = 1 → g ≠ 1 → ∃ h ∈ invCent t,
    h * g * h⁻¹ = t ∨ h * g * h⁻¹ = (x₁ * x₂) ^ 2 ∨ h * g * h⁻¹ = t * (x₁ * x₂) ^ 2
  invol_PL_distinct : (∀ h ∈ invCent t, h * t * h⁻¹ ≠ (x₁ * x₂) ^ 2) ∧
    (∀ h ∈ invCent t, h * t * h⁻¹ ≠ t * (x₁ * x₂) ^ 2) ∧
    (∀ h ∈ invCent t, h * (x₁ * x₂) ^ 2 * h⁻¹ ≠ t * (x₁ * x₂) ^ 2)

structure Ctx {G : Type} [Group G] [Finite G] (t : G) (L S : Subgroup G)
    (x₁ x₂ lam rho tau : G) : Prop extends Ctx0 t L S x₁ x₂ lam rho where
  ne_fstar : invCent t ≠ twoCore t ⊔ L
  relIndex_two : (twoCore t ⊔ L).relIndex (invCent t) = 2
  index_PT : (twoCore t ⊔ wreathGrp x₁ x₂ lam).relIndex S = 2
  card_S : Nat.card S = 2 ^ 6 * Nat.card (twoCore t)
  S_eq : S = twoCore t ⊔ m12Grp x₁ x₂ lam tau
  tau_mem : tau ∈ S
  tau_not_mem : tau ∉ twoCore t ⊔ L
  tau_sq_mem : tau ^ 2 ∈ twoCore t
  tau_x₁ : tau * x₁ * tau⁻¹ = x₁⁻¹
  tau_x₂ : tau * x₂ * tau⁻¹ = x₂⁻¹
  tau_lam : tau * lam = lam * tau
  tau_rho : tau * rho = rho * tau
  cent_L_tau : L ⊓ centralizer ({tau} : Set G) = closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam}
  perm_four : Nonempty (↥(L ⊓ centralizer ({tau} : Set G)) ≃* Equiv.Perm (Fin 4))
  cent_T_tau : wreathGrp x₁ x₂ lam ⊓ centralizer ({tau} : Set G) =
    closure {x₁ ^ 2, (x₁ * x₂) ^ 2, lam}
  dihedral : Nonempty (↥(closure {x₁ ^ 2, (x₁ * x₂) ^ 2, lam}) ≃* DihedralGroup 4)
  normal_W : NormalIn (ctxW t x₁ x₂) S
  cent_W : centralizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) = ctxW t x₁ x₂
  invol_outer : ∀ γ ∈ invCent t, γ ∉ twoCore t ⊔ L → γ ^ 2 ∈ twoCore t →
    ∃ h ∈ invCent t, ∃ p ∈ twoCore t, h * γ * h⁻¹ = p * tau
  center_ge : closure {t, (x₁ * x₂) ^ 2} ≤ S ⊓ centralizer (S : Set G)
  center_le : S ⊓ centralizer (S : Set G) ≤ twoCore t ⊔ zpowers ((x₁ * x₂) ^ 2)
  center_omega : ∀ g ∈ S ⊓ centralizer (S : Set G), g ^ 2 = 1 → g ∈ closure {t, (x₁ * x₂) ^ 2}
  m2_PT : ∀ E : Subgroup G, E ≤ twoCore t ⊔ wreathGrp x₁ x₂ lam → CFSG.Open.IsElemAbelian 2 E →
    Nat.card E ≤ 8
  m2_PT_attained : CFSG.Open.IsElemAbelian 2 (closure {t, x₁ ^ 2, (x₁ * x₂) ^ 2}) ∧
    Nat.card (closure {t, x₁ ^ 2, (x₁ * x₂) ^ 2}) = 8
  E16_cases : ∀ E : Subgroup G, E ≤ S → CFSG.Open.IsElemAbelian 2 E → Nat.card E = 16 →
    E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) = closure {t, x₁ ^ 2, (x₁ * x₂) ^ 2} ∨
    E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) = closure {t, (x₁ * x₂) ^ 2, lam} ∨
    E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) = closure {t, (x₁ * x₂) ^ 2, x₁⁻¹ * x₂ * lam}
  cent_baseGrp : invCent t ⊓ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) = ctxW t x₁ x₂
  norm_baseGrp : invCent t ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) =
    ctxW t x₁ x₂ ⊔ closure {rho, lam, tau}
  normal_norm : NormalIn (ctxW t x₁ x₂ ⊔ zpowers tau)
    (invCent t ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G))

end CFSG.OddStandard.SmallF3.HarrisU33
