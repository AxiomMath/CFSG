module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Inputs
public import CFSG.Open.GLADefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)

@[expose] def KDOutDerived : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
    (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L → ¬ AutCommInner L →
    ∀ α : MulAut L, (∃ k : ℕ, α ^ p ^ k = 1) →
      α ∈ commutator (MulAut L) ⊔ (MulAut.conj : L →* MulAut L).range →
      α ∉ (MulAut.conj : L →* MulAut L).range →
      IsLinearOrUnitaryAt p L ∨ (p = 3 ∧ 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L))

@[expose] def I294OuterDiag : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal] (z g : Y)
    (D : Subgroup Y), I294Cfg p L z g D → IsLinearOrUnitaryAt p ↥L → D ≤ L

@[expose] def SporadicOuterOddFree : Prop :=
  ∀ (s : TauCeti.SporadicName) (p : ℕ), p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (TauCeti.CFSGIndex.sporadic s).Group)

@[expose] def SporadicCentralizerPPart : Prop :=
  ∀ (s : TauCeti.SporadicName) (p : ℕ), p.Prime → p ≠ 2 →
    ∀ [Finite (TauCeti.CFSGIndex.sporadic s).Group],
    CFSG.Open.pRank p (⊤ : Subgroup (TauCeti.CFSGIndex.sporadic s).Group) = 3 →
    p ^ 4 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group →
    ∀ x : (TauCeti.CFSGIndex.sporadic s).Group, orderOf x = p →
      p ^ 3 ∣ Nat.card (Subgroup.centralizer ({x} : Set (TauCeti.CFSGIndex.sporadic s).Group))

@[expose] def I294InnerLieCross : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal] (z g : Y)
    (D : Subgroup Y), I294Cfg p L z g D → D ≤ L → ∀ d : TauCeti.ValidLieTypeIndex,
      d.1.characteristic ≠ p → Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group) → False

@[expose] def I294InnerLieLayer : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal] (z g : Y)
    (D : Subgroup Y), I294Cfg p L z g D → D ≤ L → ∀ d : TauCeti.ValidLieTypeIndex,
      d.1.characteristic = p → Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ w ∈ D, w ≠ 1 → GLAPLayer p (centralizer ({w} : Set Y)) = ⊥

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
