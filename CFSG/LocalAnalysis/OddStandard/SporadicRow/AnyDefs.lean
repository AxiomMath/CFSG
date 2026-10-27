module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporNum
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup Assembly.LowTwoRank CatLeaf

@[expose] def SporOddCompsAny (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    (S ≃* Blueprint.NativeSporadic.Carrier s) → ∀ t : S, orderOf t = 2 →
    ∀ B : Subgroup ↥(centralizer ({t} : Set S)), IsComponent B →
      ¬ OddLieOrder (Nat.card (↥B ⧸ center ↥B))

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
