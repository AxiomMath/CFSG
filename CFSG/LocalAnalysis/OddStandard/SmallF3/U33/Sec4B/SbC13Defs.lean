module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbConcl2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cos

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure Ctx13A (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau om : G) : Prop extends
    Ctx11 t L S x₁ x₂ lam rho tau where
  q_iso : IsZ4Z4E4 (ctxQ t tau x₁ x₂ rho)
  om_mem : om ∈ ctxCO t tau x₁ x₂ rho
  om_sq : om * om = 1
  om_not_mem : om ∉ closure {t, tau}
  t_om : om * t * om⁻¹ = t * tau
  CO_eq : ctxCO t tau x₁ x₂ rho = closure {t, om}
  O_cent : ctxO t tau x₁ x₂ = ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)

structure Ctx13B (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau om : G) : Prop extends
    Ctx13A t L S x₁ x₂ lam rho tau om where
  Q_comm : ∀ a ∈ ctxQ t tau x₁ x₂ rho, ∀ b ∈ ctxQ t tau x₁ x₂ rho, a * b = b * a
  sq_V : ∀ a ∈ ctxQ t tau x₁ x₂ rho, a ^ 2 ∈ fourGrp x₁ x₂
  Y_elem : CFSG.Open.IsElemAbelian 2 (ctxYq t tau x₁ x₂ rho)
  V_le_Y : fourGrp x₁ x₂ ≤ ctxYq t tau x₁ x₂ rho
  normal_Y : NormalIn (ctxYq t tau x₁ x₂ rho) (ctxM t tau x₁ x₂)
  fpf_YV : S4B.FpfSetting (ctxYq t tau x₁ x₂ rho) (fourGrp x₁ x₂) rho
  fpf_QY : S4B.FpfSetting (ctxQ t tau x₁ x₂ rho) (ctxYq t tau x₁ x₂ rho) rho

structure Ctx13C (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau om : G) : Prop extends
    Ctx13B t L S x₁ x₂ lam rho tau om where
  tau_cent_Y : ∀ a ∈ ctxYq t tau x₁ x₂ rho, tau * a = a * tau
  om_cent_Y : ∀ a ∈ ctxYq t tau x₁ x₂ rho, om * a = a * om
  tau_inv_Q : ∀ a ∈ ctxQ t tau x₁ x₂ rho, tau * a * tau⁻¹ = a⁻¹
  Y_cent : ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) = fourGrp x₁ x₂ ∧
    ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) = fourGrp x₁ x₂
  Y_comm : ⁅ctxYq t tau x₁ x₂ rho, zpowers t⁆ = fourGrp x₁ x₂ ∧
    ⁅ctxYq t tau x₁ x₂ rho, zpowers (t * tau)⁆ = fourGrp x₁ x₂

structure Ctx13D (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau om : G) : Prop extends
    Ctx13C t L S x₁ x₂ lam rho tau om where
  lam_om : lam * om * lam⁻¹ = om
  Q_om : Ctx13Om t tau x₁ x₂ rho om
  Q_omtau : Ctx13Om t tau x₁ x₂ rho (om * tau)

end CFSG.OddStandard.SmallF3.HarrisU33
