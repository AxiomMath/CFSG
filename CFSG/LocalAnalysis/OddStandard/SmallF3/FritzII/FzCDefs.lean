module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzAssump
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41Defs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

structure FzCCtx (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G)
    (x₁ x₂ lam rho : G) : Prop where
  simple : IsSimpleGroup G
  ass : FzAssumptionII G
  ctx : Ctx0 t L S x₁ x₂ lam rho
  eq_PL : invCent t = twoCore t ⊔ L

@[expose] def FzCSy1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G),
    FzCCtx G t L S x₁ x₂ lam rho → Nat.card (twoCore t) = 2 →
    FzSylow (l41V S t x₁ x₂) → t ∉ fzP t x₁ x₂ rho → False

@[expose] def FzCSy2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G),
    FzCCtx G t L S x₁ x₂ lam rho → Nat.card (twoCore t) = 2 →
    FzSylow (l41V S t x₁ x₂) → t ∈ fzP t x₁ x₂ rho → False

@[expose] def FzCSy3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G),
    FzCCtx G t L S x₁ x₂ lam rho → Nat.card (twoCore t) = 4 →
    FzSylow (l41V S t x₁ x₂) → False

@[expose] def FzCSy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G),
    FzCCtx G t L S x₁ x₂ lam rho → FzSylow (l41V S t x₁ x₂) → False

@[expose] def FzCNS1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G),
    FzCCtx G t L S x₁ x₂ lam rho → 2 ∣ (l41V S t x₁ x₂).index →
    2 ∣ (l41V1 t x₁ x₂ rho lam).index → False

@[expose] def FzCNS2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G),
    FzCCtx G t L S x₁ x₂ lam rho → 2 ∣ (l41V S t x₁ x₂).index →
    ¬ 2 ∣ (l41V1 t x₁ x₂ rho lam).index → False

@[expose] def FzCNS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (x₁ x₂ lam rho : G),
    FzCCtx G t L S x₁ x₂ lam rho → 2 ∣ (l41V S t x₁ x₂).index → False

end CFSG.OddStandard.SmallF3.FritzII
