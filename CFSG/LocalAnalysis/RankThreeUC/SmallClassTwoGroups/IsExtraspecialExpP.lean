module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups

open Subgroup

def IsExtraspecialExpP (p n : ℕ) (Q : Type) [Group Q] : Prop :=
  Nat.card Q = p ^ (1 + 2 * n) ∧ Monoid.exponent Q = p ∧
    commutator Q = center Q ∧ Nat.card (center Q) = p

end CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups
