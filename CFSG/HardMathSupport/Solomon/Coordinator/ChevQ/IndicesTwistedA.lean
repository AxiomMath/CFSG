module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Indices

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

theorem not_excIndex_twistedA {p r : ℕ} {q : TauCeti.PrimePower} (h1 : ¬ IsTwoPow q 1)
    (h3 : ¬ IsTwoPow q 3) : ¬ ExcIndex p (.twistedA r q) := by
  intro hX
  rcases hX with hB | ⟨-, hL | hG | hB2 | hT | hS⟩
  · simp only [Bal207Index] at hB
    rcases hB with ⟨-, ⟨hq, -⟩ | ⟨hq, -⟩⟩
    · exact hq.elim h1 h3
    · exact h1 hq
  · simp [IsL2EightIndex] at hL
  · simp only [Gen2318Index] at hG
    exact hG.1.elim h1 h3
  · simp [Bal209TwoIndex] at hB2
  · simp [IsTwistedE6FourIndex] at hT
  · rcases hS with hF | hD | hF4
    · simp [IsF4EightIndex] at hF
    · simp [IsD4FourIndex] at hD
    · simp only [FourIndex] at hF4
      exact h3 hF4.1

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
