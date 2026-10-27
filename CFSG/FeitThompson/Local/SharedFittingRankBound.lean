module

public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.HighFittingRankUniqueOvergroupWitness

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {H M : Subgroup G}

theorem elementaryAbelianPRank_mixedFitting_le_two [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hH : IsCoatom H) (hM : IsCoatom M) (hHM : H ≠ M) (hFM : mixedFitting H ≤ M)
    (hp : p.Prime) : elementaryAbelianPRank p ↥(mixedFitting H) ≤ 2 := by
  by_contra hle
  obtain ⟨X, -, hXF, hX⟩ := exists_bot_lt_isUniqueMaximalOvergroup_le_mixedFitting hna hodd hsolv
    hH hp (not_le.1 hle)
  exact hHM (hX.eq_of_isCoatom hM (hXF.trans hFM)).symm

theorem forall_prime_elementaryAbelianPRank_mixedFitting_le_two [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hH : IsCoatom H) (hM : IsCoatom M) (hHM : H ≠ M) (hFM : mixedFitting H ≤ M) :
    ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(mixedFitting H) ≤ 2 :=
  fun _ hq => elementaryAbelianPRank_mixedFitting_le_two hna hodd hsolv hH hM hHM hFM hq

end

end CFSG.FeitThompson
