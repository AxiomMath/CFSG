module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AConcl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemFus
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemFusB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AProd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemCls
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemXB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4

theorem fusion_tz (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    conjIn (normalizer (S : Set G)) t = t • (zpowers ((x₁ * x₂) ^ 2) : Set G) :=
  S4A.fusion_tz_of_l42 hc.toCtx hc.l42

theorem not_conj_z (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    ¬ ∃ g : G, g * t * g⁻¹ = (x₁ * x₂) ^ 2 :=
  S4A.not_conj_z_of_ctx hc.toCtx

theorem tG_inf_four (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    ∀ g : G, ∀ v ∈ fourGrp x₁ x₂, g * t * g⁻¹ ≠ v :=
  S4A.tG_inf_four_of_ctx hc.toCtx

theorem card_S_seven (hc : Ctx4 t L S x₁ x₂ lam rho tau) : Nat.card S = 2 ^ 7 :=
  S4A.card_S_of hc.toCtx hc.l43

theorem m12Rel (hc : Ctx4 t L S x₁ x₂ lam rho tau) : M12Rel x₁ x₂ lam tau :=
  S4A.m12Rel_of_ctx hc.toCtx hc.l44.1

theorem S_eq_prod (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    S = zpowers t ⊔ m12Grp x₁ x₂ lam tau ∧ zpowers t ⊓ m12Grp x₁ x₂ lam tau = ⊥ :=
  S4A.S_eq_prod_of hc.toCtx hc.l43 hc.l44.1

theorem center_S (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    S ⊓ centralizer (S : Set G) = closure {t, (x₁ * x₂) ^ 2} :=
  S4A.center_S_of hc.toCtx hc.l43

theorem centralizer_t_tau (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    centralizer ((closure {t, tau} : Subgroup G) : Set G) =
      closure {t, tau} ⊔ closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} ∧
    CFSG.Open.IsElemAbelian 2 (closure {t, tau} : Subgroup G) ∧
    Nat.card (closure {t, tau} : Subgroup G) = 4 ∧
    closure {t, tau} ⊓ closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} = (⊥ : Subgroup G) ∧
    (∀ a ∈ (closure {t, tau} : Subgroup G),
      ∀ b ∈ (closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} : Subgroup G), a * b = b * a) :=
  S4A.centralizer_t_tau_of hc.toCtx hc.l43 hc.l44.1

theorem five_classes (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    (∀ g ∈ invCent t, g * g = 1 → g ≠ 1 → ∃ h ∈ invCent t,
      h * g * h⁻¹ = t ∨ h * g * h⁻¹ = (x₁ * x₂) ^ 2 ∨ h * g * h⁻¹ = tau ∨
      h * g * h⁻¹ = t * (x₁ * x₂) ^ 2 ∨ h * g * h⁻¹ = t * tau) ∧
    List.Pairwise (fun a b : G => ∀ h ∈ invCent t, h * a * h⁻¹ ≠ b)
      [t, (x₁ * x₂) ^ 2, tau, t * (x₁ * x₂) ^ 2, t * tau] :=
  S4A.five_classes_of hc.toCtx hc.l43 hc.l44.1

theorem involutions_tau_coset (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    (∀ u ∈ L, (tau * u) * (tau * u) = 1 → ∃ c ∈ L, c * tau * c⁻¹ = tau * u) ∧
    (∀ u ∈ L, (t * tau * u) * (t * tau * u) = 1 → ∃ c ∈ L, c * (t * tau) * c⁻¹ = t * tau * u) :=
  S4A.involutions_tau_coset_of hc.toCtx hc.l43 hc.l44.1

theorem ctxX_facts (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    CFSG.Open.IsElemAbelian 2 (ctxX t tau x₁ x₂) ∧ Nat.card (ctxX t tau x₁ x₂) = 16 ∧
    centralizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G) = ctxX t tau x₁ x₂ ∧
    invCent t ⊓ ctxM t tau x₁ x₂ = ctxW t x₁ x₂ ⊔ closure {tau, rho, lam} :=
  ⟨(S4A.ctxX_elemAbelian_of hc.toCtx hc.l44.1).1, (S4A.ctxX_elemAbelian_of hc.toCtx hc.l44.1).2,
    S4A.centralizer_X_of hc.toCtx hc.l43 hc.l44.1, S4A.normalizer_X_of hc.toCtx hc.l43 hc.l44.1⟩

theorem exists_action_on_X (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    ∃ ρ : ↥(ctxM t tau x₁ x₂) →* MulAut ↥(ctxX t tau x₁ x₂),
      (∀ (m : ↥(ctxM t tau x₁ x₂)) (x : ↥(ctxX t tau x₁ x₂)),
        ((ρ m x : ↥(ctxX t tau x₁ x₂)) : G) = (m : G) * (x : G) * (m : G)⁻¹) ∧
      ∀ m : ↥(ctxM t tau x₁ x₂), ρ m = 1 ↔ (m : G) ∈ ctxX t tau x₁ x₂ :=
  S4A.exists_action_on_X_of hc.toCtx hc.l43 hc.l44.1

end Ctx4

end CFSG.OddStandard.SmallF3.HarrisU33
