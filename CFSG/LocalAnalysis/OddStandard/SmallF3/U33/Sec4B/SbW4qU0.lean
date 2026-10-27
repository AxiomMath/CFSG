module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4q0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4q_O_le_U (t tau x₁ x₂ lam : G) : ctxO t tau x₁ x₂ ≤ ctxU t tau x₁ x₂ lam :=
  le_sup_left

theorem w4q_lam_mem_U (t tau x₁ x₂ lam : G) : lam ∈ ctxU t tau x₁ x₂ lam :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers lam)

theorem w4q_X_le_U
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) :
    ctxX t tau x₁ x₂ ≤ ctxU t tau x₁ x₂ lam :=
  (w4q_X_le_O hc).trans (w4q_O_le_U t tau x₁ x₂ lam)

theorem w4q_U_le_M (hc : Ctx4C t L S x₁ x₂ lam rho tau) :
    ctxU t tau x₁ x₂ lam ≤ ctxM t tau x₁ x₂ := hc.U_sylow.1

theorem w4q_U_norm_X (hc : Ctx4C t L S x₁ x₂ lam rho tau) {u x : G}
    (hu : u ∈ ctxU t tau x₁ x₂ lam) (hx : x ∈ ctxX t tau x₁ x₂) :
    u * x * u⁻¹ ∈ ctxX t tau x₁ x₂ := by
  have hM : u ∈ Subgroup.normalizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G) :=
    w4q_U_le_M hc hu
  exact ((Subgroup.mem_normalizer_iff.mp hM) x).mp hx

theorem w4q_U_norm_O (hc : Ctx4C t L S x₁ x₂ lam rho tau) {u o : G}
    (hu : u ∈ ctxU t tau x₁ x₂ lam) (ho : o ∈ ctxO t tau x₁ x₂) :
    u * o * u⁻¹ ∈ ctxO t tau x₁ x₂ :=
  (p0_normal_O t tau x₁ x₂).2 u (w4q_U_le_M hc hu) o ho

theorem w4q_lam_not_mem_O (hc : Ctx4C t L S x₁ x₂ lam rho tau) : lam ∉ ctxO t tau x₁ x₂ :=
  (w4q_toW4Ctxc hc).lam_not_mem_O

theorem w4q_card_U
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxU t tau x₁ x₂ lam) = 2 ^ 9 :=
  w4_card_U (w4q_toW4Ctxc hc).toW4Ctxb

theorem w4q_card_U_eq
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxU t tau x₁ x₂ lam) = 2 * Nat.card ↥(ctxO t tau x₁ x₂) := by
  rw [w4q_card_U hc, hc.card_O]
  norm_num

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
