module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AConcl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbDefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure W4Ctx0 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Ctx10 t L S x₁ x₂ lam rho tau where
  tM : conjIn (ctxM t tau x₁ x₂) t = t • (fourGrp x₁ x₂ : Set G)

structure W4Ctxa (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    W4Ctx0 t L S x₁ x₂ lam rho tau where
  card_M : Nat.card (ctxM t tau x₁ x₂) = 3 * 2 ^ 9
  normal_V : NormalIn (fourGrp x₁ x₂) (ctxM t tau x₁ x₂)
  normal_E : NormalIn (ctxE t x₁ x₂) (ctxM t tau x₁ x₂)

structure W4Ctxb (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    W4Ctxa t L S x₁ x₂ lam rho tau where
  O_eq_C : ctxO t tau x₁ x₂ =
    ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)
  card_O : Nat.card (ctxO t tau x₁ x₂) = 2 ^ 8
  lam_not_mem_O : lam ∉ ctxO t tau x₁ x₂

structure W4Ctxc (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    W4Ctxb t L S x₁ x₂ lam rho tau where
  M_eq : ctxM t tau x₁ x₂ = ctxO t tau x₁ x₂ ⊔ closure {rho, lam}
  S_le_U : S ≤ ctxU t tau x₁ x₂ lam
  U_sylow : IsSylowIn 2 (ctxU t tau x₁ x₂ lam) (ctxM t tau x₁ x₂)

end CFSG.OddStandard.SmallF3.HarrisU33
