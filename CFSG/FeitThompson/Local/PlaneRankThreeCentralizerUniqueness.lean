module

public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.UniquenessTransferCentralizerRankTwo
import CFSG.FeitThompson.OddOrder.RankThreeUniquenessMaximalOvergroup
import CFSG.FeitThompson.OddOrder.RankTwoKernelSmallerComplementPrimes
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup
import CFSG.FeitThompson.Local.OutsideSigmaSylowCentralPrimeElement
public import Mathlib.GroupTheory.Solvable

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p q : ℕ} {E : Subgroup G}

theorem exists_isUniqueMaximalOvergroup_of_plane_of_three_le_elementaryAbelianPRank_centralizer
    [Finite G] [IsSimpleGroup G] (hp : p.Prime) (hq : q.Prime) (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hEea : IsElementaryAbelian p E) (hEcard : Nat.card ↥E = p ^ 2)
    (hrank : 3 ≤ elementaryAbelianPRank q ↥(centralizer (E : Set G))) :
    ∃ M : Subgroup G, IsUniqueMaximalOvergroup E M := by
  have hEbot : E ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hEcard
    exact (Nat.one_lt_pow two_ne_zero hp.one_lt).ne' hEcard.symm
  obtain ⟨e, heE, he1⟩ := E.bot_or_exists_ne_one.resolve_left hEbot
  obtain ⟨C, hCcent, hcomm, hexp, hCcard⟩ :=
    (mem_elementaryAbelianRanks_subgroup_iff (H := centralizer (E : Set G)) (d := 3) hq).1
      ((le_elementaryAbelianPRank_iff hq.one_lt).1 hrank)
  have hCea : IsElementaryAbelian q C :=
    isElementaryAbelian_iff.2
      ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a a.2 b b.2), hexp⟩
  have hCtop : C ≠ ⊤ := by
    intro h
    refine (centralizer_singleton_lt_top hna he1).ne (top_le_iff.1 ?_)
    rw [← h]
    exact fun x hx =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hCcent hx) e heE).symm
  have hCrank : 3 ≤ maxElementaryAbelianPRank ↥C :=
    le_maxElementaryAbelianPRank (mem_elementaryAbelianPrimeRanks.2
      ⟨q, hq, hCea.mem_elementaryAbelianRanks_of_le hq hCcard le_rfl⟩)
  obtain ⟨M, hM⟩ := exists_isUniqueMaximalOvergroup_of_three_le_maxElementaryAbelianPRank
    hna hodd hsolv hCtop hCrank
  have hCbot : ⊥ < C := bot_lt_iff_ne_bot.2 fun h => by
    rw [h, Subgroup.card_bot] at hCcard
    exact (Nat.one_lt_pow three_ne_zero hq.one_lt).ne' hCcard.symm
  have hEC : E ≤ centralizer (C : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun c hc => (mem_centralizer_iff.1 (hCcent hc) x hx).symm
  exact ⟨M, isUniqueMaximalOvergroup_of_le_centralizer hp hna hodd hsolv hCbot hM hEC
    (hEea.le_elementaryAbelianPRank hp hEcard le_rfl)⟩

theorem existsUnique_isCoatom_ge_of_plane_of_three_le_elementaryAbelianPRank_centralizer
    [Finite G] [IsSimpleGroup G] (hp : p.Prime) (hq : q.Prime) (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hEea : IsElementaryAbelian p E) (hEcard : Nat.card ↥E = p ^ 2)
    (hrank : 3 ≤ elementaryAbelianPRank q ↥(centralizer (E : Set G))) :
    ∃! M : Subgroup G, IsCoatom M ∧ E ≤ M := by
  obtain ⟨M, hM⟩ :=
    exists_isUniqueMaximalOvergroup_of_plane_of_three_le_elementaryAbelianPRank_centralizer
      hp hq hna hodd hsolv hEea hEcard hrank
  exact ⟨M, ⟨hM.isCoatom, hM.le⟩, fun N hN => hM.eq_of_isCoatom hN.1 hN.2⟩

theorem exists_isCoatom_ge_of_plane_of_three_le_elementaryAbelianPRank_centralizer
    [Finite G] [IsSimpleGroup G] (hp : p.Prime) (hq : q.Prime) (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hEea : IsElementaryAbelian p E) (hEcard : Nat.card ↥E = p ^ 2)
    (hrank : 3 ≤ elementaryAbelianPRank q ↥(centralizer (E : Set G))) :
    ∃ M : Subgroup G, IsCoatom M ∧ E ≤ M := by
  obtain ⟨M, hM⟩ :=
    exists_isUniqueMaximalOvergroup_of_plane_of_three_le_elementaryAbelianPRank_centralizer
      hp hq hna hodd hsolv hEea hEcard hrank
  exact ⟨M, hM.isCoatom, hM.le⟩

end

end CFSG.FeitThompson
