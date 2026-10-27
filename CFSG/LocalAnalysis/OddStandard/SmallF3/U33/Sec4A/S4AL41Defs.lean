module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ADefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

structure L41Ctx {G : Type} [Group G] [Finite G] (t : G) (L S : Subgroup G)
    (x₁ x₂ lam rho : G) : Prop extends Ctx0 t L S x₁ x₂ lam rho where
  eq_PL : invCent t = twoCore t ⊔ L
  glob : Sec4Glob G
  inputs : Sec4Inputs

variable {G : Type} [Group G]

@[expose] def Sec4SectionIso (C N : Subgroup G) (K : Type) [Group K] : Prop :=
  ∃ φ : ↥C →* K, Function.Surjective φ ∧ φ.ker = N.subgroupOf C

@[expose] def l41N (t x₁ x₂ : G) : Subgroup G :=
  normalizer ((ctxE t x₁ x₂ : Subgroup G) : Set G)

@[expose] def l41O2 (t x₁ x₂ : G) : Subgroup G := CFSG.Open.pCoreOf 2 (l41N t x₁ x₂)

@[expose] def l41V (S : Subgroup G) (t x₁ x₂ : G) : Subgroup G := l41O2 t x₁ x₂ ⊔ S

@[expose] def l41R (t x₁ x₂ rho : G) : Subgroup G := ⁅l41O2 t x₁ x₂, zpowers rho⁆

@[expose] def l41F (t x₁ x₂ rho : G) : Subgroup G := l41R t x₁ x₂ rho ⊔ zpowers t

@[expose] def l41Y (t x₁ x₂ rho : G) : Subgroup G :=
  closure {g | g ∈ l41R t x₁ x₂ rho ∧ g * g = 1}

@[expose] def l41M (t x₁ x₂ rho : G) : Subgroup G :=
  normalizer ((l41F t x₁ x₂ rho : Subgroup G) : Set G)

@[expose] def l41Q (t x₁ x₂ rho : G) : Subgroup G := CFSG.Open.pCoreOf 2 (l41M t x₁ x₂ rho)

@[expose] def l41Q1 (t x₁ x₂ rho : G) : Subgroup G := ⁅l41Q t x₁ x₂ rho, zpowers rho⁆

@[expose] def l41V1 (t x₁ x₂ rho lam : G) : Subgroup G := l41Q1 t x₁ x₂ rho ⊔ closure {t, lam}

end CFSG.OddStandard.SmallF3.HarrisU33
