module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ADefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Ctx

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

@[expose] def Lemma4_1Concl (t : G) (L : Subgroup G) : Prop :=
  invCent t ≠ twoCore t ⊔ L

@[expose] def Lemma4_2Concl (S : Subgroup G) : Prop := 2 ∣ S.index

@[expose] def Lemma4_3Concl (t : G) : Prop := twoCore t = zpowers t

@[expose] def Lemma4_4Concl (t tau : G) : Prop := tau ^ 2 = 1 ∧ ∀ g : G, g ^ 2 ≠ t

structure Ctx4 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop
    extends Ctx t L S x₁ x₂ lam rho tau where
  l42 : Lemma4_2Concl S
  l43 : Lemma4_3Concl t
  l44 : Lemma4_4Concl t tau

@[expose] def Lemma4_5Concl (t : G) (S : Subgroup G) (x₁ x₂ tau : G) : Prop :=
  ∀ V : Subgroup G, NormalIn V S → CFSG.Open.IsElemAbelian 2 V → Nat.card V = 4 →
    (∀ g : G, ∀ v ∈ V, g * t * g⁻¹ ≠ v) →
    V = fourGrp x₁ x₂ ∧
    S ⊓ centralizer (V : Set G) = zpowers t ⊔ closure {x₁, x₂, tau} ∧
    ⁅S ⊓ centralizer (V : Set G), S ⊓ centralizer (V : Set G)⁆ = V

@[expose] def Lemma4_6Concl (t : G) (S : Subgroup G) (x₁ x₂ tau : G) : Prop :=
  ∀ V : Subgroup G, NormalIn V S → CFSG.Open.IsElemAbelian 2 V → Nat.card V = 8 →
    V = closure {x₁ ^ 2, (x₁ * x₂) ^ 2, t} ∨ V = closure {x₁ ^ 2, (x₁ * x₂) ^ 2, tau} ∨
    V = closure {x₁ ^ 2, (x₁ * x₂) ^ 2, t * tau} ∨
    V = closure {x₁ ^ 2, (x₁ * x₂) ^ 2, tau * (x₁ * x₂)} ∨
    V = closure {x₁ ^ 2, (x₁ * x₂) ^ 2, t * tau * (x₁ * x₂)}

@[expose] def Lemma4_7aConcl (t : G) (S : Subgroup G) (x₁ x₂ : G) : Prop :=
  ∀ Y : Subgroup G, IsE16In S Y →
    closure {t, (x₁ * x₂) ^ 2} = S ⊓ centralizer (S : Set G) ∧
    closure {t, (x₁ * x₂) ^ 2} ≤ Y ∧ S ⊓ centralizer (Y : Set G) = Y

@[expose] def Lemma4_7bConcl (t : G) (S : Subgroup G) (x₁ x₂ tau : G) : Prop :=
  ∀ Y : Subgroup G, IsE16In S Y → NormalIn Y S →
    Y = closure {t, (x₁ * x₂) ^ 2, x₁ ^ 2, tau} ∨
    Y = closure {t, (x₁ * x₂) ^ 2, x₁ ^ 2, tau * (x₁ * x₂)}

@[expose] def Lemma4_7cConcl (t : G) (S : Subgroup G) (x₁ x₂ tau : G) : Prop :=
  ∀ Y : Subgroup G, IsE16In S Y → x₁ ^ 2 ∈ Y →
    Y ≤ zpowers t ⊔ (baseGrp x₁ x₂ ⊔ zpowers tau) ∧
    ∃ a ∈ baseGrp x₁ x₂, a * tau ∈ Y ∧ Y = closure {t, x₁ ^ 2, (x₁ * x₂) ^ 2, a * tau}

@[expose] def Lemma4_7dConcl (t : G) (S : Subgroup G) (x₁ x₂ lam tau : G) : Prop :=
  ∀ Y : Subgroup G, IsE16In S Y → x₁ ^ 2 ∉ Y →
    ∃ a ∈ baseGrp x₁ x₂, ∃ b ∈ baseGrp x₁ x₂, a * lam ∈ Y ∧ b * tau ∈ Y ∧
      Y = closure {t, (x₁ * x₂) ^ 2, a * lam, b * tau}

@[expose] def Lemma4_7eConcl (t : G) (S : Subgroup G) (x₁ x₂ tau : G) : Prop :=
  ∀ Y : Subgroup G, IsE16In S Y →
    (conjIn (invCent t) ((x₁ * x₂) ^ 2) ∩ (Y : Set G)).ncard = 3 ∧
    (conjIn (invCent t) (t * (x₁ * x₂) ^ 2) ∩ (Y : Set G)).ncard = 3 ∧
    (conjIn (invCent t) tau ∩ (Y : Set G)).ncard = 4 ∧
    (conjIn (invCent t) (t * tau) ∩ (Y : Set G)).ncard = 4

@[expose] def Lemma4_7Concl (t : G) (S : Subgroup G) (x₁ x₂ lam tau : G) : Prop :=
  Lemma4_7aConcl t S x₁ x₂ ∧ Lemma4_7bConcl t S x₁ x₂ tau ∧ Lemma4_7cConcl t S x₁ x₂ tau ∧
    Lemma4_7dConcl t S x₁ x₂ lam tau ∧ Lemma4_7eConcl t S x₁ x₂ tau

@[expose] def Lemma4_8aConcl (t : G) (x₁ x₂ rho tau : G) : Prop :=
  (∃ g : G, g * tau * g⁻¹ = t) ↔
    ∃ g ∈ ctxM t tau x₁ x₂ ⊓ normalizer ((closure {t, tau} : Subgroup G) : Set G),
      g * tau * g⁻¹ = t ∧
      g ∈ centralizer ((closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho} : Subgroup G) : Set G)

@[expose] def Lemma4_8bConcl (t : G) (x₁ x₂ rho tau : G) : Prop :=
  (∃ g : G, g * (t * tau) * g⁻¹ = t) ↔
    ∃ g ∈ ctxM t tau x₁ x₂ ⊓ normalizer ((closure {t, tau} : Subgroup G) : Set G),
      g * (t * tau) * g⁻¹ = t ∧
      g ∈ centralizer ((closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho} : Subgroup G) : Set G)

@[expose] def Lemma4_8Concl (t : G) (x₁ x₂ rho tau : G) : Prop :=
  Lemma4_8aConcl t x₁ x₂ rho tau ∧ Lemma4_8bConcl t x₁ x₂ rho tau

@[expose] def Lemma4_9Concl (t : G) (S : Subgroup G) (x₁ x₂ tau : G) : Prop :=
  (∀ 𝒮 : Sylow 2 G, S < (𝒮 : Subgroup G) → ctxS1 S (𝒮 : Subgroup G) ≤ ctxM t tau x₁ x₂) ∧
  (conjIn (ctxM t tau x₁ x₂) t = t • (fourGrp x₁ x₂ : Set G) ∨
    conjIn (ctxM t tau x₁ x₂) t =
      t • (fourGrp x₁ x₂ : Set G) ∪ tau • (fourGrp x₁ x₂ : Set G) ∨
    conjIn (ctxM t tau x₁ x₂) t =
      t • (fourGrp x₁ x₂ : Set G) ∪ (t * tau) • (fourGrp x₁ x₂ : Set G) ∨
    conjIn (ctxM t tau x₁ x₂) t =
      t • (fourGrp x₁ x₂ : Set G) ∪ tau • (fourGrp x₁ x₂ : Set G) ∪
        (t * tau) • (fourGrp x₁ x₂ : Set G))

@[expose] def Lemma4_10Concl (t : G) (x₁ x₂ tau : G) : Prop :=
  (conjIn (ctxM t tau x₁ x₂) t).ncard = 4 ∨ (conjIn (ctxM t tau x₁ x₂) t).ncard = 8

structure Ctx10 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop
    extends Ctx4 t L S x₁ x₂ lam rho tau where
  l45 : Lemma4_5Concl t S x₁ x₂ tau
  l46 : Lemma4_6Concl t S x₁ x₂ tau
  l47 : Lemma4_7Concl t S x₁ x₂ lam tau
  l48 : Lemma4_8Concl t x₁ x₂ rho tau
  l49 : Lemma4_9Concl t S x₁ x₂ tau
  l410 : Lemma4_10Concl t x₁ x₂ tau

end CFSG.OddStandard.SmallF3.HarrisU33
