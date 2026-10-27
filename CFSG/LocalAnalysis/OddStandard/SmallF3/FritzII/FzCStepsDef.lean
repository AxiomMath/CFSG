module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41Facts

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure FzCSteps (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G) : Prop where
  ctx : Ctx0 t L S x₁ x₂ lam rho
  basic : L41Basic t S x₁ x₂ lam rho
  fusion : L41Fusion t S x₁ x₂ lam
  orbit_t : conjIn (l41N t x₁ x₂) t = t • (fourGrp x₁ x₂ : Set G)
  O2_eq : l41O2 t x₁ x₂ = l41N t x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)
  card_O2 : Nat.card (l41O2 t x₁ x₂) = 4 * Nat.card (ctxW t x₁ x₂)
  N_eq : l41N t x₁ x₂ = l41O2 t x₁ x₂ ⊔ closure {rho, lam}
  V_le : l41V S t x₁ x₂ ≤ l41N t x₁ x₂
  V_pGroup : IsPGroup 2 (l41V S t x₁ x₂)
  V_sylow : ¬ 2 ∣ (l41V S t x₁ x₂).relIndex (l41N t x₁ x₂)
  card_V : Nat.card (l41V S t x₁ x₂) = 8 * Nat.card (ctxW t x₁ x₂)

end CFSG.OddStandard.SmallF3.FritzII
