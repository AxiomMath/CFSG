module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbDefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Lemma4_15Concl (t tau x₁ x₂ rho : G) : Prop :=
  ∀ B : Subgroup G, B ⋖ (ctxQ t tau x₁ x₂ rho ⊔ zpowers tau) →
    CFSG.Open.IsElemAbelian 2 (B ⊓ centralizer (B : Set G)) →
    Nat.card (B ⊓ centralizer (B : Set G) : Subgroup G) = 16 →
    B ⊓ centralizer (B : Set G) = ctxYq t tau x₁ x₂ rho

@[expose] def Lemma4_16Concl (t tau x₁ x₂ rho om : G) : Prop :=
  CharIn (ctxYq t tau x₁ x₂ rho) (ctxQ t tau x₁ x₂ rho ⊔ closure {tau, om}) ∧
  CharIn (ctxQ t tau x₁ x₂ rho) (ctxQ t tau x₁ x₂ rho ⊔ closure {tau, om}) ∧
  CharIn (ctxQ t tau x₁ x₂ rho ⊔ zpowers tau) (ctxQ t tau x₁ x₂ rho ⊔ closure {tau, om}) ∧
  CharIn (closure {tau, om} ⊔ ctxYq t tau x₁ x₂ rho) (ctxQ t tau x₁ x₂ rho ⊔ closure {tau, om}) ∧
  CharIn (zpowers tau ⊔ ctxYq t tau x₁ x₂ rho) (ctxQ t tau x₁ x₂ rho ⊔ closure {tau, om})

@[expose] def FstarConcl (t : G) : Prop :=
  t ∉ CFSG.generalizedFitting G ∧ CFSG.generalizedFitting G ⊔ zpowers t = ⊤ ∧
    ((Nat.card (CFSG.generalizedFitting G)).factorization 2 = 11 ∨
      (Nat.card (CFSG.generalizedFitting G)).factorization 2 = 12)

@[expose] def YUniqueConcl (t tau x₁ x₂ rho : G) (𝒮 : Subgroup G) : Prop :=
  ∀ R : Subgroup G, IsPGroup 2 R → 𝒮 ≤ R →
    NormalIn (ctxYq t tau x₁ x₂ rho) R ∧ IsE16In R (ctxYq t tau x₁ x₂ rho) ∧
    ∀ A : Subgroup G, IsE16In R A → NormalIn A R → A = ctxYq t tau x₁ x₂ rho

@[expose] def Lemma4_17Concl (t tau x₁ x₂ rho om : G) (𝒮 : Subgroup G) : Prop :=
  FstarConcl t ∧
  (IsZ4pow 4 (ctxK t tau x₁ x₂ rho ⊓ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G)) ∧
    ctxK t tau x₁ x₂ rho ⊓ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) ⊓
      centralizer ({rho} : Set G) = ⊥) ∧
  (CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho) =
      (ctxK t tau x₁ x₂ rho ⊓ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G)) ⊔
        closure {t, om} ∧
    ⁅CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho), zpowers rho⁆ =
      ctxK t tau x₁ x₂ rho ⊓ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) ∧
    CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho) ⊓ centralizer ({rho} : Set G) =
      closure {t, om}) ∧
  (NormalIn (ctxYq t tau x₁ x₂ rho) (ctxK t tau x₁ x₂ rho) ∧
    ctxK t tau x₁ x₂ rho ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) =
      (ctxK t tau x₁ x₂ rho ⊓ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G)) ⊔
        closure {tau, om}) ∧
  YUniqueConcl t tau x₁ x₂ rho 𝒮

@[expose] def Lemma4_18Concl (t tau x₁ x₂ lam rho om : G) (𝒮 : Subgroup G) : Prop :=
  FstarConcl t ∧ YUniqueConcl t tau x₁ x₂ rho 𝒮 ∧
  (NormalIn (ctxYq t tau x₁ x₂ rho) (ctxK t tau x₁ x₂ rho) ∧
    ctxK t tau x₁ x₂ rho = CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho) ⊔ closure {rho, lam} ∧
    CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho) =
      (ctxK t tau x₁ x₂ rho ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G)) ⊔
        zpowers t ∧
    ⁅CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho), zpowers rho⁆ =
      ⁅ctxK t tau x₁ x₂ rho ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G),
        zpowers rho⁆ ∧
    (⁅⁅CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho), zpowers rho⁆,
        ⁅CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho), zpowers rho⁆⁆ ≠ ⊥ ∧
      ⁅⁅⁅CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho), zpowers rho⁆,
          ⁅CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho), zpowers rho⁆⁆,
        ⁅CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho), zpowers rho⁆⁆ = ⊥) ∧
    ⁅CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho), zpowers rho⁆ ⊓
      centralizer ({rho} : Set G) = ⊥ ∧
    ctxK t tau x₁ x₂ rho ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) ⊓
      centralizer ({rho} : Set G) = closure {tau, om})

end CFSG.OddStandard.SmallF3.HarrisU33
