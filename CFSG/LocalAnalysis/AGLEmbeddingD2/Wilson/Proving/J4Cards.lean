module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Sporadic.J4
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem card_J4_factorization_eleven :
    (Nat.card NativeSporadic.J4).factorization 11 = 3 := by
  rw [CFSG.Sporadic.J4.card_J4]
  have h : (86775571046077562880 : ℕ) =
      11 ^ 3 * (2 ^ 21 * 3 ^ 3 * 5 * 7 * 23 * 29 * 31 * 37 * 43) := by norm_num
  rw [h, Nat.factorization_mul (show (11 : ℕ) ^ 3 ≠ 0 by norm_num)
      (show (2 ^ 21 * 3 ^ 3 * 5 * 7 * 23 * 29 * 31 * 37 * 43 : ℕ) ≠ 0 by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd
      (show ¬ 11 ∣ (2 ^ 21 * 3 ^ 3 * 5 * 7 * 23 * 29 * 31 * 37 * 43 : ℕ) by norm_num),
    add_zero]

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
