module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Extremal
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Defs

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def Prop51 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∃ B : Subgroup G, IsExtremal B

@[expose] def Lemma52 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∃ b ∈ B, b ≠ 1 ∧ upsilonOf B b ≠ ⊥

@[expose] def Lemma53 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBOneMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G, IsUpsilonComponent B b L →
      ∀ x ∈ B, x ≠ 1 → InducesFieldAut 3 L x →
        (⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)),
          GLBConj g (GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)))) ≤ upsilonOf B x

@[expose] def Lemma54 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBOneMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G, IsUpsilonComponent B b L →
      ∀ A : Subgroup G, A ≤ B → (∀ a ∈ A, InducesFieldAut 3 L a) → CFSG.Open.pRank 3 A ≤ 2

@[expose] def Lemma55 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsElemAbelian 3 B → 4 ≤ CFSG.Open.pRank 3 B → ∀ b ∈ B, b ≠ 1 →
      ∀ A : Subgroup G, IsEkIn 3 3 B A → ∀ L : Subgroup G,
        GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L →
        (∀ a ∈ A, InducesFieldAut 3 L a) →
        (∀ a ∈ A, a ≠ 1 → b ∈ oPrimePOf 3 (Subgroup.centralizer ({a} : Set G))) →
        IsBZeroMax 3 B ∧
          ∀ x ∈ B, x ≠ 1 → ⁅upsilonOf B x, Subgroup.zpowers b⁆ ≤ GLAPPrimeCoreOf 3 (upsilonOf B x)

@[expose] def Lemma56 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 →
      (∀ L : Subgroup G, GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L →
        (IsSLThree (barOf 3 L) ∨ IsSUThree (barOf 3 L)) → B ≤ Subgroup.normalizer (L : Set G)) ∧
      ∀ L : Subgroup G, IsUpsilonComponent B b L → B ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lemma57 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → IsWeaklyBalancedWrt 3 2 B

@[expose] def Lemma58 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ B' : Subgroup G, IsElemAbelian 3 B' → 4 ≤ CFSG.Open.pRank 3 B' →
      3 ≤ CFSG.Open.pRank 3 (B ⊓ B') →
        IsBOneMax 3 B' ∧ ∃ E : Subgroup G, IsEkIn 3 3 (B ⊓ B') E ∧ Even (Nat.card (alphaE 3 2 E))

@[expose] def Lemma59 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G,
      IsUpsilonComponent B b L → ¬ IsHatON (barOf 3 L)

end CFSG.HardMathSupport.Solomon.LocalBalance
