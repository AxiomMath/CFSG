module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12Data
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndData

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M12

open CFSG.ComponentClassification.M12Cover CFSG.Monster.B.Co2

@[expose] def m12OverOdd : Prop :=
  ∀ y ∈ blockGroup, y ≠ 1 → y ^ 1485 = 1 → ∃ c ∈ blockGroup,
    c * permOfArr 24 (m12T0 m12E0) = permOfArr 24 (m12T0 m12E0) * c ∧
      (y * (c * y * c⁻¹)) ^ 1485 ≠ 1

@[expose] def m12OverFacts (S : Array (Array ℕ)) : Prop :=
  m12OverOdd ∧ m12OverCentOK S m12E0 m12OverCW = true ∧ m12OverHOK S m12E0 m12OverH0 = true

end CFSG.ComponentClassification.RankTwoSporadic.M12

end
