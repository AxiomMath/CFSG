module

public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.HighRankFittingUniqueOvergroup
import CFSG.FeitThompson.OddOrder.RankTwoKernelSmallerComplementPrimes
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {q : ℕ} {M L : Subgroup G}

theorem elementaryAbelianPRank_mixedFitting_inf_le_two
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hM : IsCoatom M) (hL : IsCoatom L) (hML : M ≠ L) (hq : q.Prime) :
    elementaryAbelianPRank q ↥(mixedFitting M ⊓ L) ≤ 2 := by
  by_contra hcon
  have h3 : 3 ≤ elementaryAbelianPRank q ↥(mixedFitting M ⊓ L) := by omega
  obtain ⟨E, hEle, hcomm, hexp, hEcard⟩ :=
    (mem_elementaryAbelianRanks_subgroup_iff (H := mixedFitting M ⊓ L) (d := 3) hq).1
      ((le_elementaryAbelianPRank_iff hq.one_lt).1 h3)
  have hEea : IsElementaryAbelian q E := isElementaryAbelian_iff.2
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a a.2 b b.2), hexp⟩
  have hEF : E ≤ mixedFitting M := hEle.trans inf_le_left
  have hEL : E ≤ L := hEle.trans inf_le_right
  have hErank : 3 ≤ elementaryAbelianPRank q ↥E := hEea.le_elementaryAbelianPRank hq hEcard le_rfl
  have hFrank : 3 ≤ elementaryAbelianPRank q ↥(mixedFitting M) :=
    hEea.le_elementaryAbelianPRank hq hEcard hEF
  obtain ⟨N, hN⟩ := exists_isUniqueMaximalOvergroup_of_three_le_elementaryAbelianPRank_mixedFitting
    hna hodd hsolv hM hq hFrank hEea.isMulCommutative hEea.isPGroup hErank
  exact hML ((hN.eq_of_isCoatom hM (hEF.trans (mixedFitting_le M))).trans
    (hN.eq_of_isCoatom hL hEL).symm)

end

end CFSG.FeitThompson
