module

public import CFSG.LieType.BorelTits.SpecialLinear
public import CFSG.LieType.BorelTits.CentralQuotient
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LieType.BorelTits

open CFSG.Assembly.LowTwoRank

theorem holds_statedProj_statedSL (n : ℕ) (K : Type) [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] : Holds (StatedProj (StatedSL n K)) p :=
  Holds.statedProj _ (holds_statedSL n K p)

theorem holds_projectiveSpecialLinearGroup (n : ℕ) (K : Type) [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] : Holds (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) p :=
  (holds_statedProj_statedSL n K p).of_mulEquiv
    (projectiveSpecialLinearGroupEquivStatedProj n K).symm

end CFSG.LieType.BorelTits
