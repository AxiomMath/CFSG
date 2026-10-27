module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type*} [Group G]

@[expose] def IsEkIn (p k : ℕ) (B D : Subgroup G) : Prop :=
  D ≤ B ∧ IsElemAbelian p D ∧ Nat.card D = p ^ k

@[expose] def IsBalancedWrt (p k : ℕ) (B : Subgroup G) : Prop :=
  ∀ D : Subgroup G, IsEkIn p k B D → ∀ x ∈ B, x ≠ 1 →
    GLADelta p D ⊓ Subgroup.centralizer ({x} : Set G) ≤
      GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))

@[expose] def IsWeaklyBalancedWrt (p k : ℕ) (B : Subgroup G) : Prop :=
  ∀ D : Subgroup G, IsEkIn p k B D → ∀ x ∈ B, x ≠ 1 →
    ⁅GLADelta p D ⊓ Subgroup.centralizer ({x} : Set G), B⁆ ≤
      GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))

@[expose] def thetaAt (p k : ℕ) (A : Subgroup G) (a : G) : Subgroup G :=
  ⨆ (D : Subgroup G) (_ : IsEkIn p k A D), Subgroup.centralizer ({a} : Set G) ⊓ GLADelta p D

@[expose] def thetaStarAt (p k : ℕ) (A : Subgroup G) (a : G) : Subgroup G :=
  thetaAt p k A a ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G))

@[expose] def thetaClosure (p k : ℕ) (A : Subgroup G) : Subgroup G :=
  ⨆ (D : Subgroup G) (_ : IsEkIn p k A D), GLADelta p D

@[expose] def thetaStarClosure (p k : ℕ) (A : Subgroup G) : Subgroup G :=
  thetaClosure p k A ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G))

@[expose] def alphaE (p k : ℕ) (E : Subgroup G) : Subgroup G :=
  (⨆ (D : Subgroup G) (_ : IsEkIn p k E D), ⁅GLADelta p D, E⁆) ⊔ GLADelta p E

@[expose] noncomputable def coreIn [Finite G] (p k : ℕ) (P X : Subgroup G) : Subgroup G :=
  ⨆ (Q : Subgroup G) (_ : Q ≤ P ∧ k ≤ pRank p Q), X ⊓ Subgroup.normalizer (Q : Set G)

@[expose] def bClosure (B L : Subgroup G) : Subgroup G :=
  ⨆ (b : G) (_ : b ∈ B), GLBConj b L

@[expose] def IsInGOne [Finite G] (p : ℕ) (B L : Subgroup G) : Prop :=
  bClosure B L = coreIn p 3 B (bClosure B L)

@[expose] noncomputable def psiOf [Finite G] (p : ℕ) (B : Subgroup G) (b : G) : Subgroup G :=
  sSup {L | GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L ∧
    ¬ IsStronglyLocallyOneBalanced p B b L ∧ IsInGOne p B L}

@[expose] noncomputable def psiStar [Finite G] (p : ℕ) (B : Subgroup G) (b : G) : Subgroup G :=
  psiOf p B b ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) ⊔
    GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set G))

@[expose] noncomputable def psiStarGroup [Finite G] (p : ℕ) (B : Subgroup G) : Subgroup G :=
  ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), psiStar p B b

@[expose] def GLCaseOne (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∃ B : Subgroup G, IsBOneMax p B ∧ IsBalancedWrt p 2 B ∧ lambdaStarGroup p B = psiStarGroup p B

@[expose] def GLCaseTwo (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop :=
  p ≤ 5 ∧ 5 ≤ GLATwoLocalRank p G ∧ ¬ GLCaseOne G p

@[expose] def GLCaseThree (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop :=
  p = 5 ∧ GLATwoLocalRank p G = 4 ∧ ¬ GLCaseOne G p

@[expose] def GLCaseFour (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop :=
  p = 3 ∧ GLATwoLocalRank p G = 4 ∧ ¬ GLCaseOne G p

@[expose] def Prop21 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B : Subgroup G, GLAIsBmax p B → IsBalancedWrt p 3 B ∧ (5 < p → IsBalancedWrt p 2 B)

@[expose] def Prop22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∃ B : Subgroup G, IsBZeroMax p B ∧ IsWeaklyBalancedWrt p 2 B

@[expose] def Prop41 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    (∃ B : Subgroup G, IsBOneMax p B ∧ IsBalancedWrt p 3 B ∧ IsWeaklyBalancedWrt p 2 B) ∧
      (GLCaseOne G p ∨ GLCaseTwo G p ∨ GLCaseThree G p ∨ GLCaseFour G p)

@[expose] def Prop42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    (GLCaseOne G p ∨ GLCaseTwo G p ∨ GLCaseThree G p) →
      ∃ B : Subgroup G, IsBOneMax p B ∧ ∃ M₀ : Subgroup G, IsPreUniquenessSubgroup p B M₀

@[expose] def CaseFourPreUniqueness : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p → GLCaseFour G p →
    ∃ B : Subgroup G, IsBOneMax p B ∧ ∃ M₀ : Subgroup G, IsPreUniquenessSubgroup p B M₀

end CFSG.HardMathSupport.Solomon.Coordinator
