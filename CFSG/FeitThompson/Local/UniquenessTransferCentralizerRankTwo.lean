module

public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup
import CFSG.FeitThompson.OddOrder.RankTwoKernelSmallerComplementPrimes
import CFSG.FeitThompson.Local.CentralizerControlUniqueMaximalOvergroup
import CFSG.FeitThompson.Local.OutsideSigmaSylowCentralPrimeElement
public import Mathlib.GroupTheory.Solvable

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {L M K : Subgroup G}

theorem centralizer_le_of_isUniqueMaximalOvergroup [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hLM : IsUniqueMaximalOvergroup L M)
    (hKL : K ≤ centralizer (L : Set G)) {b : G} (hb : b ∈ K) (hb1 : b ≠ 1) :
    centralizer ({b} : Set G) ≤ M :=
  hLM.le_of_ne_top
    (fun x hx => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hKL hb) x hx))
    (centralizer_singleton_lt_top hna hb1).ne

theorem isUniqueMaximalOvergroup_of_le_centralizer [IsSimpleGroup G] (hp : p.Prime)
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hL : ⊥ < L) (hLM : IsUniqueMaximalOvergroup L M) (hKL : K ≤ centralizer (L : Set G))
    (hrank : 2 ≤ elementaryAbelianPRank p ↥K) :
    IsUniqueMaximalOvergroup K M := by
  obtain ⟨l, hlL, hl⟩ := L.bot_or_exists_ne_one.resolve_left hL.ne'
  have hKtop : K ≠ ⊤ := by
    intro h
    refine (centralizer_singleton_lt_top hna hl).ne (top_le_iff.mp (h ▸ ?_))
    exact fun x hx =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hKL hx) l hlL).symm)
  obtain ⟨B, hBK, hcomm, hexp, hBcard⟩ :=
    (mem_elementaryAbelianRanks_subgroup_iff (H := K) (d := 2) hp).mp
      ((le_elementaryAbelianPRank_iff hp.one_lt).mp hrank)
  have hBe : IsElementaryAbelian p B :=
    isElementaryAbelian_iff.mpr
      ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a a.2 b b.2), hexp⟩
  have hcent : ∀ b ∈ B, b ≠ 1 → centralizer ({b} : Set G) ≤ M := fun b hb =>
    centralizer_le_of_isUniqueMaximalOvergroup hna hLM hKL (hBK hb)
  have hBM : B ≤ M := fun b hb => by
    rcases eq_or_ne b 1 with rfl | hb1
    · exact one_mem M
    · exact hcent b hb hb1 (mem_centralizer_singleton_iff.mpr rfl)
  exact (isUniqueMaximalOvergroup_of_centralizer_le hp hna hodd hsolv hLM.isCoatom hBe hBcard
    le_rfl hBM hcent).mono hBK hKtop

theorem le_of_le_centralizer [IsSimpleGroup G] (hp : p.Prime) (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hL : ⊥ < L) (hLM : IsUniqueMaximalOvergroup L M) (hKL : K ≤ centralizer (L : Set G))
    (hrank : 2 ≤ elementaryAbelianPRank p ↥K) :
    K ≤ M :=
  (isUniqueMaximalOvergroup_of_le_centralizer hp hna hodd hsolv hL hLM hKL hrank).le

end

end CFSG.FeitThompson
