module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSp4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSpSocle

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

theorem hinFor_symplectic_odd : HinFor fun Y _ => ∃ n ℓ f : ℕ, ℓ ≠ 2 ∧
    Assembly.LowTwoRank.StatedClassicalModel Y .PSp n ℓ f := by
  intro Y _ _ _ ⟨n, ℓ, f, hℓ2, hY⟩ hnab p m hp hp2 hm h16 _ τ hτ hL
  obtain ⟨⟨hℓ, -, hn2, -⟩, -⟩ := id hY
  rcases Nat.lt_or_ge n 3 with hn | hn
  · obtain rfl : n = 2 := by omega
    exact hinConcl_psp4 hnab hℓ hℓ2 hY hp hp2 hm h16 hτ hL
  · exact (false_of_psp_ge_three hnab hn hℓ hℓ2 hY hp hp2 hm h16 hτ hL).elim

end CFSG.ComponentClassification.HarrisLit.Hin
