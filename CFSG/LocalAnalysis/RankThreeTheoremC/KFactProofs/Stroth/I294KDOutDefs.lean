module

public import CFSG.Blueprint.Catalog
public import CFSG.Open.LocalVocabulary
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Inputs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)

@[expose] def D4ThreeRankFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (ℓ f : ℕ), StatedClassicalModel X .POmegaPlus 4 ℓ f →
    4 ≤ pRank 3 (⊤ : Subgroup X)

@[expose] def E6ThreeRankFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (ℓ f : ℕ), ChevalleyExceptionalModel X .E6 ℓ f →
    3 ∣ ℓ ^ f - 1 → 4 ≤ pRank 3 (⊤ : Subgroup X)

@[expose] def TwistedE6ThreeRankFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (ℓ f : ℕ), ChevalleyExceptionalModel X .twistedE6 ℓ f →
    4 ≤ pRank 3 (⊤ : Subgroup X)

theorem isLinearOrUnitaryAt_of_psl {L : Type} [Group L] {p n ℓ f : ℕ}
    (h : StatedClassicalModel L .PSL n ℓ f) (hn : p ∣ n) (hq : p ∣ ℓ ^ f - 1) :
    IsLinearOrUnitaryAt p L := by
  obtain ⟨-, K, instF, instFin, hK, he⟩ := h
  exact Or.inl ⟨n, K, instF, instFin, hn, by rw [hK]; exact hq, he⟩

theorem isLinearOrUnitaryAt_of_psu {L : Type} [Group L] {p n ℓ f : ℕ}
    (h : StatedClassicalModel L .PSU n ℓ f) (hn : p ∣ n) (hq : p ∣ ℓ ^ f + 1) :
    IsLinearOrUnitaryAt p L := by
  obtain ⟨-, K, instF, instFin, hK, he⟩ := h
  exact Or.inr ⟨n, ℓ ^ f, K, instF, instFin, hK, hn, hq, he⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
