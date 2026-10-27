module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalStep73
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem symplecticTwoOut : SymplecticTwoOut := by
  intro G _ _ A D hD hq hA _
  cases D with
  | symplectic n m hn hm hnm K hK e =>
    have hm1 : m = 1 := by
      have h : 2 ^ m = 2 ^ 1 := hq
      exact Nat.pow_right_injective le_rfl h
    subst hm1
    have hn3 : 3 ≤ n := by
      by_contra h
      exact hnm (Prod.ext (show n = 2 by omega) (show 2 ^ 1 = 2 by norm_num))
    have : Group.IsPerfect ↥A := (Group.isPerfect_def).2 hA.1
    have h := (perfect_symplectic_central_quotient_outer_prime_control Nat.prime_two le_rfl
      (by omega : 2 ≤ n) hK ↥A ⟨e⟩).2.2.2.1 hn3
    norm_num at h
    change Odd (Nat.card (Outer ↥A))
    rw [h]
    exact odd_one
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
