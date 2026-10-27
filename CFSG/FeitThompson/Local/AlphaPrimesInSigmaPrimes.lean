module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.AlphaCore
public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
import CFSG.FeitThompson.OddOrder.SigmaSylowIsAmbientSylow
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.RankTwoKernelSmallerComplementPrimes
import CFSG.FeitThompson.OddOrder.RankThreeUniquenessMaximalOvergroup
import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ} {M : Subgroup G}

theorem mem_sigmaPrimes_of_mem_alphaPrimes [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) (hp : p ∈ alphaPrimes ↥M) : p ∈ sigmaPrimes M := by
  obtain ⟨hpp, hrank⟩ := mem_alphaPrimes.1 hp
  have := Fact.mk hpp
  have h3 : (3 : ℕ) ∈ elementaryAbelianRanks p ↥M :=
    (le_elementaryAbelianPRank_iff hpp.one_lt).1 hrank
  obtain ⟨E, hEM, hcomm, hexp, hcard⟩ := (mem_elementaryAbelianRanks_subgroup_iff hpp).1 h3
  have hEea : IsElementaryAbelian p E := isElementaryAbelian_iff.2
    ⟨IsMulCommutative.of_comm fun x y => Subtype.ext (hcomm x x.2 y y.2), hexp⟩
  obtain ⟨S, hS⟩ := (hEea.isPGroup.comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
  set P : Subgroup G := (S : Subgroup ↥M).map M.subtype with hPdef
  have hEP : E ≤ P := by
    rw [hPdef, ← Subgroup.map_subgroupOf_eq_of_le hEM]
    exact Subgroup.map_mono hS
  have hPM : P ≤ M := Subgroup.map_subtype_le _
  have hPrank : 3 ≤ maxElementaryAbelianPRank ↥P :=
    le_trans (hEea.le_elementaryAbelianPRank hpp hcard hEP)
      (elementaryAbelianPRank_le_maxElementaryAbelianPRank hpp)
  have hPtop : P ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hPM))
  obtain ⟨N, hN⟩ := exists_isUniqueMaximalOvergroup_of_three_le_maxElementaryAbelianPRank
    hna hodd hsolv hPtop hPrank
  have hN' : IsUniqueMaximalOvergroup P M := by
    rw [hN.eq_of_isCoatom hM hPM]; exact hN
  have hEbot : E ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hcard
    exact hpp.one_lt.ne' (by simpa using hcard.symm)
  have hPbot : P ≠ ⊥ := fun h => hEbot (le_bot_iff.1 (h ▸ hEP))
  have hlt := normalizer_lt_top_of_isPGroup hna hpp hPbot (S.isPGroup'.map M.subtype)
  refine mem_sigmaPrimes_iff.2 ⟨hpp, ?_, S, hN'.le_of_ne_top Subgroup.le_normalizer hlt.ne⟩
  exact (one_le_elementaryAbelianPRank_iff hpp).1 (le_trans (by norm_num) hrank)

theorem alphaPrimes_subset_sigmaPrimes [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M) :
    alphaPrimes ↥M ⊆ sigmaPrimes M :=
  fun _ hp => mem_sigmaPrimes_of_mem_alphaPrimes hna hodd hsolv hM hp

theorem natCard_eq_pow_factorization_of_mem_alphaPrimes [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M)
    (hp : p ∈ alphaPrimes ↥M) {P : Subgroup G} (hPM : P ≤ M)
    (hPcard : Nat.card P = p ^ (Nat.card M).factorization p) :
    Nat.card P = p ^ (Nat.card G).factorization p :=
  natCard_eq_pow_factorization_of_mem_sigmaPrimes
    (mem_sigmaPrimes_of_mem_alphaPrimes hna hodd hsolv hM hp) hPM hPcard

theorem exists_sylow_coe_eq_of_mem_alphaPrimes [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M)
    (hp : p ∈ alphaPrimes ↥M) (S : Sylow p ↥M) :
    ∃ T : Sylow p G, (T : Subgroup G) = (S : Subgroup ↥M).map M.subtype :=
  exists_sylow_coe_eq_map_subtype (mem_sigmaPrimes_of_mem_alphaPrimes hna hodd hsolv hM hp) S

theorem map_subtype_alphaCore_le_sigmaCore [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M) :
    (alphaCore ↥M).map M.subtype ≤ sigmaCore M := by
  rw [sigmaCore_eq_map_piCore, alphaCore_eq_piCore]
  exact Subgroup.map_mono (piCore_mono (alphaPrimes_subset_sigmaPrimes hna hodd hsolv hM))

end

end CFSG.FeitThompson
