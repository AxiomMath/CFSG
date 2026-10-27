module

public import CFSG.RankThree.PartOne.SEITZ5.UPair
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUOddProof

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs

open CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne.SEITZ5 (subfieldPairSUF2Odd_of_four_le)

theorem subfieldPairSUOddTwo_holds : SubfieldPairSUOddTwo := by
  intro ℓ f f₀ K _ h k h₀ hbar p hp hp2 hf hq n hn _ A hne
  obtain ⟨hℓ, hf₀⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 hq
  subst hℓ
  subst hf₀
  exact subfieldPairSUF2Odd_of_four_le hn f 1 K h k h₀ hbar p hp hp2 hf rfl A hne

end CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs
