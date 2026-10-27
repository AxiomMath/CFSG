module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Blueprint.Recognition.Exact

open Assembly.LowTwoRank

@[expose] def EvenBNRankTwoType (X : Type) [Group X] : Prop :=
  ∃ (t : StatedLieTag) (n f : ℕ), 1 ≤ f ∧
    (t, n) ∈ ({(.PSL, 3), (.PSU, 4), (.PSU, 5), (.PSp, 2), (.G2, 0),
      (.trialityD4, 0), (.twistedF4, 0), (.Tits, 0)} : Set (StatedLieTag × ℕ)) ∧
    LieModel X t n 2 f

end CFSG.Blueprint.Recognition.Exact
