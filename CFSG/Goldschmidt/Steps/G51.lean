module

public import CFSG.Goldschmidt.StatementsG2

public section

namespace CFSG.Goldschmidt

theorem G51_of (h55 : S_G55) (h56 : S_G56) : S_G51 := by
  intro G _ _ S A hset a ha ha1 H hH
  by_cases haO : a ∈ GorensteinWalter.qCoreOf H 2
  · by_cases hp : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
        3 ≤ CFSG.Open.pRank p (GorensteinWalter.qCoreOf H p)
    · exact Or.inl (h56 G S A hset a ha ha1 H hH hp)
    · refine Or.inr ⟨haO, fun p hp' hp2 => ?_⟩
      by_contra hlt
      exact hp ⟨p, hp', hp2, by omega⟩
  · exact Or.inl (h55 G S A hset a ha ha1 H hH haO)

end CFSG.Goldschmidt
