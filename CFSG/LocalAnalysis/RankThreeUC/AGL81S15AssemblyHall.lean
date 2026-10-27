module

public import CFSG.GroupTheory.HallFactorizedPRank

public section

open scoped Pointwise

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem exists_isHallSubgroup_twoPrime_of_cartan {Y : Type} [Group Y] [Finite Y]
    (hY : Group.IsSolvable Y) {C N Hc : Subgroup Y}
    (hsup : (C : Set Y) * (N : Set Y) = Set.univ)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hHc : IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} Hc)
    (h3 : 3 ≤ CFSG.Open.pRank q Hc) :
    ∃ H : Subgroup Y, IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H ∧
      H = H ⊓ C ⊔ H ⊓ N ∧ 3 ≤ CFSG.Open.pRank q H := by
  refine CFSG.exists_isHallSubgroup_eq_sup_inf_of_le_pRank (G := Y) hY
    (A := C) (B := N) hsup (π := {p : Nat.Primes | (p : ℕ) ≠ 2}) (Hc := Hc) hHc hq ?_ h3
  change q ≠ 2
  exact hq2

end CFSG.LocalAnalysis.RankThreeUC.S15
