module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292LinUniDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.Blueprint Subgroup

@[expose] def KD291DefCharL : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
    (∃ a b : L, a * b ≠ b * a) →
    (∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = p ∧
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)) →
    3 ≤ Open.pRank p (⊤ : Subgroup L) → ∀ y : L, orderOf y = p →
      Open.pRank p (centralizer ({y} : Set L)) ≤ 2 →
      Open.pRank p (⊤ : Subgroup L) = 3 ∧
        (StatedClassicalModel L .PSp 2 p 1 ∨ ChevalleyExceptionalModel L .G2 p 1)

@[expose] def KD291Nilp : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y) (L : Subgroup Y),
    LinUniCfg p P x z L → LinUniShape p x L →
      CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set Y))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
