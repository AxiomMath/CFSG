module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallIdent
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def SmallIdentAtP (K : Type) [Group K] [Finite K] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ T : Sylow p K, ¬ IsCyclic (T : Subgroup K) →
    GLBCore p 1 (T : Subgroup K) ≠ ⊤ → Open.pRank p (⊤ : Subgroup K) ≤ 2 → IsSmallStrongP p K

@[expose] def OneLieIdentAtP (K : Type) [Group K] [Finite K] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ T : Sylow p K, ¬ IsCyclic (T : Subgroup K) →
    GLBCore p 1 (T : Subgroup K) ≠ ⊤ → ¬ Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
      ∃ d : TauCeti.ValidLieTypeIndex,
        ((∃ n : ℕ, 3 ≤ n ∧ IsLinTwoIndex p n d) ∨
          (IsUnitaryIndex p d ∧ 2 ≤ d.1.fieldExponent) ∨ IsReeGTwoIndex p d) ∧
        Nonempty (K ≃* CatGroup d)

@[expose] def SmallIdentAlt : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n : ℕ), 5 ≤ n → Nonempty (K ≃* alternatingGroup (Fin n)) →
    ∀ p : ℕ, SmallIdentAtP K p

@[expose] def SmallIdentLieCharP : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (K ≃* CatGroup d) →
      ∀ p : ℕ, p = d.1.characteristic → SmallIdentAtP K p

@[expose] def SmallIdentLieOffChar : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (K ≃* CatGroup d) →
      ∀ p : ℕ, p ≠ d.1.characteristic → SmallIdentAtP K p

@[expose] def SmallIdentSporAt (s : TauCeti.SporadicName) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic s).Group) → ∀ p : ℕ, SmallIdentAtP K p

@[expose] def OneLieIdentAlt : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n : ℕ), 5 ≤ n → Nonempty (K ≃* alternatingGroup (Fin n)) →
    ∀ p : ℕ, OneLieIdentAtP K p

@[expose] def OneLieIdentLieCharP : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (K ≃* CatGroup d) →
      ∀ p : ℕ, p = d.1.characteristic → OneLieIdentAtP K p

@[expose] def OneLieIdentLieOffChar : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (K ≃* CatGroup d) →
      ∀ p : ℕ, p ≠ d.1.characteristic → OneLieIdentAtP K p

@[expose] def OneLieIdentSporAt (s : TauCeti.SporadicName) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic s).Group) → ∀ p : ℕ, OneLieIdentAtP K p

@[expose] def IsRankOneLieIndex (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, d = .A 1 q) ∨ (∃ q : TauCeti.PrimePower, d = .twistedA 2 q) ∨
    ∃ m : ℕ, d = .reeG2 m

@[expose] def IsLinThreeFourIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q

@[expose] def CharPGen : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (K ≃* CatGroup d) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p = d.1.characteristic → ¬ IsRankOneLieIndex d.1 →
        ∀ T : Sylow p K, GLBCore p 1 (T : Subgroup K) = ⊤

@[expose] def OffCharGen : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (K ≃* CatGroup d) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
        ∀ T : Sylow p K, ¬ IsCyclic (T : Subgroup K) → ¬ (p = 3 ∧ IsLinThreeFourIndex d) →
          ¬ (p = 5 ∧ d.1 = .tits) → GLBCore p 1 (T : Subgroup K) = ⊤

@[expose] def OffCharAut : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (K ≃* CatGroup d) →
      ∀ p : ℕ, (p = 3 ∧ IsLinThreeFourIndex d) ∨ (p = 5 ∧ d.1 = .tits) →
        Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2

end CFSG.AGLEmbedding
