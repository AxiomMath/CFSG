module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AConcl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbDefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Lemma4_11Concl (t tau x₁ x₂ : G) : Prop :=
  (conjIn (ctxM t tau x₁ x₂) t).ncard ≠ 4

structure Ctx11 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Ctx10 t L S x₁ x₂ lam rho tau where
  tM : conjIn (ctxM t tau x₁ x₂) t =
    t • (fourGrp x₁ x₂ : Set G) ∪ (t * tau) • (fourGrp x₁ x₂ : Set G)
  card_M : Nat.card (ctxM t tau x₁ x₂) = 3 * 2 ^ 10
  normal_N : NormalIn (ctxN tau x₁ x₂) (ctxM t tau x₁ x₂)
  normal_V : NormalIn (fourGrp x₁ x₂) (ctxM t tau x₁ x₂)
  card_O : Nat.card (ctxO t tau x₁ x₂) = 2 ^ 9
  M_eq : ctxM t tau x₁ x₂ = ctxO t tau x₁ x₂ ⊔ closure {rho, lam}
  tM_O : conjIn (ctxO t tau x₁ x₂) t = conjIn (ctxM t tau x₁ x₂) t
  tauM : conjIn (ctxM t tau x₁ x₂) tau = tau • (fourGrp x₁ x₂ : Set G)
  tauO : conjIn (ctxO t tau x₁ x₂) tau = tau • (fourGrp x₁ x₂ : Set G)
  center_O : ctxO t tau x₁ x₂ ⊓ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) =
    fourGrp x₁ x₂
  cent_trho : ctxM t tau x₁ x₂ ⊓ centralizer ((closure {t, tau, rho} : Subgroup G) : Set G) =
    closure {t, tau, rho}
  CO_dihedral : Nonempty (↥(ctxCO t tau x₁ x₂ rho) ≃* DihedralGroup 4)
  CO_center : ctxCO t tau x₁ x₂ rho ⊓ centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) =
    zpowers tau
  S_le_U : S ≤ ctxU t tau x₁ x₂ lam
  U_sylow : IsSylowIn 2 (ctxU t tau x₁ x₂ lam) (ctxM t tau x₁ x₂)
  X_le_R : ctxX t tau x₁ x₂ ≤ ctxR t tau x₁ x₂
  R_le_O : ctxR t tau x₁ x₂ ≤ ctxO t tau x₁ x₂
  card_R : Nat.card (ctxR t tau x₁ x₂) = 2 ^ 8
  normal_R : NormalIn (ctxR t tau x₁ x₂) (ctxM t tau x₁ x₂)
  R_quot : (∀ a ∈ ctxR t tau x₁ x₂, a ^ 2 ∈ ctxX t tau x₁ x₂) ∧
    ∀ a ∈ ctxR t tau x₁ x₂, ∀ b ∈ ctxR t tau x₁ x₂, a * b * a⁻¹ * b⁻¹ ∈ ctxX t tau x₁ x₂
  R_eq : ctxR t tau x₁ x₂ = ctxQ t tau x₁ x₂ rho ⊔ ctxX t tau x₁ x₂
  normal_Q : NormalIn (ctxQ t tau x₁ x₂ rho) (ctxM t tau x₁ x₂)
  base_le_Q : baseGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho
  phi_Q : fourGrp x₁ x₂ ≤ ctxPhi (ctxQ t tau x₁ x₂ rho) ∧
    ctxPhi (ctxQ t tau x₁ x₂ rho) ≤ ctxX t tau x₁ x₂
  O_eq : ctxO t tau x₁ x₂ = ctxR t tau x₁ x₂ ⊔ ctxCO t tau x₁ x₂ rho
  CR_rho : ctxR t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) = closure {t, tau}
  tR : conjIn (ctxR t tau x₁ x₂) t = t • (fourGrp x₁ x₂ : Set G)
  ttauR : conjIn (ctxR t tau x₁ x₂) (t * tau) = (t * tau) • (fourGrp x₁ x₂ : Set G)
  tauR : conjIn (ctxR t tau x₁ x₂) tau = tau • (fourGrp x₁ x₂ : Set G)

end CFSG.OddStandard.SmallF3.HarrisU33
