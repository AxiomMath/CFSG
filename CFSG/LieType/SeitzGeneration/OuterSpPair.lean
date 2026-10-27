module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSp

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.PartOne.CTP

@[expose] def SubfieldPairSpOdd : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (k : Subfield K) (p : ℕ), p.Prime → p ≠ 2 →
    Nat.card K = Nat.card k ^ p → ∀ r : ℕ, 2 ≤ r → ∀ A : gsp r K,
      (spSub r k).map (conjSp r K A).toMonoidHom ≠ spSub r k →
      Subgroup.closure ((spSub r k : Set (StatedSp r K)) ∪
        ((spSub r k).map (conjSp r K A).toMonoidHom : Set (StatedSp r K))) = ⊤

end CFSG.LieType.SeitzGeneration
