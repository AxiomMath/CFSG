module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import CFSG.FeitThompson.Definitions.MaximumElementaryAbelianPrimeRank
import CFSG.FeitThompson.Local.ScnRankThreeUniqueMaximalOvergroup
import CFSG.FeitThompson.Local.HighRankAbelianUniquenessCentralizers
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.SecondCenterPlaneCharacteristicCentralizer
import CFSG.FeitThompson.Local.PrimeCentralizerMinimalFittingAbelian
import CFSG.FeitThompson.OddOrder.RankTwoKernelSmallerComplementPrimes
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.CategoryTheory.Category.Init

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G]

theorem exists_isUniqueMaximalOvergroup_of_three_le_maxElementaryAbelianPRank [Finite G]
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    {X : Subgroup G} (hX : X ≠ ⊤) (hrank : 3 ≤ maxElementaryAbelianPRank ↥X) :
    ∃ M : Subgroup G, IsUniqueMaximalOvergroup X M := by
  obtain ⟨p, hp, hmem⟩ := mem_elementaryAbelianPrimeRanks.1
    (maxElementaryAbelianPRank_mem_elementaryAbelianPrimeRanks ↥X)
  have h3 : (3 : ℕ) ∈ elementaryAbelianRanks p ↥X := mem_elementaryAbelianRanks_of_le hrank hmem
  obtain ⟨E, hEX, hcomm, hexp, hcard⟩ :=
    (mem_elementaryAbelianRanks_subgroup_iff (H := X) (d := 3) hp).1 h3
  have hEea : IsElementaryAbelian p E := isElementaryAbelian_iff.2
    ⟨IsMulCommutative.of_comm fun x y => Subtype.ext (hcomm x x.2 y y.2), hexp⟩
  have hErank : 3 ≤ elementaryAbelianPRank p ↥E :=
    hEea.le_elementaryAbelianPRank hp hcard le_rfl
  have hpodd : Odd p := hodd.of_dvd_nat
    ((dvd_pow_self p three_ne_zero).trans (hcard ▸ E.card_subgroup_dvd_card))
  have := Fact.mk hp
  obtain ⟨P, hEP⟩ := hEea.isPGroup.exists_le_sylow
  have hPrank : 3 ≤ elementaryAbelianPRank p ↥(P : Subgroup G) :=
    hEea.le_elementaryAbelianPRank hp hcard hEP
  obtain ⟨A, hAnormal, hAcomm, hArank, hAself⟩ :=
    exists_abelian_normal_centralizer_eq_of_three_le_elementaryAbelianPRank_of_isPGroup hp hpodd
      P.isPGroup' hPrank
  set A' : Subgroup G := A.map (P : Subgroup G).subtype with hA'def
  have hA'P : A' ≤ (P : Subgroup G) := Subgroup.map_subtype_le A
  have hA'sub : A'.subgroupOf (P : Subgroup G) = A :=
    Subgroup.comap_map_eq_self_of_injective (P : Subgroup G).subtype_injective A
  have hA'self : centralizer (A' : Set G) ⊓ (P : Subgroup G) = A' := by
    rw [hA'def, centralizer_map_subtype_inf, hAself]
  have hA'rank : 3 ≤ elementaryAbelianPRank p ↥A' := by
    rw [hA'def, ← elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt
      (A.equivMapOfInjective (P : Subgroup G).subtype (P : Subgroup G).subtype_injective)]
    exact hArank
  have hA'comm : IsMulCommutative ↥A' := by
    have := hAcomm
    rw [hA'def]
    infer_instance
  have hA'pg : IsPGroup p ↥A' := P.isPGroup'.to_le hA'P
  have hAM : ∃ M : Subgroup G, IsUniqueMaximalOvergroup A' M :=
    exists_isUniqueMaximalOvergroup_of_scn_three_le_elementaryAbelianPRank hna hodd hsolv hp P
      (hA'sub ▸ hAnormal) hA'self hA'rank
  obtain ⟨N, hN⟩ := exists_isUniqueMaximalOvergroup_of_three_le_elementaryAbelianPRank_centralizer
    hp hna hodd hsolv hA'pg hA'rank hAM hEea.isPGroup
    (not_isCyclic_of_three_le_elementaryAbelianPRank hp hErank)
    (hEea.le_elementaryAbelianPRank hp hcard (hEea.le_centralizer le_rfl))
  exact ⟨N, hN.mono hEX hX⟩

theorem existsUnique_isCoatom_ge_of_three_le_maxElementaryAbelianPRank [Finite G]
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    {X : Subgroup G} (hX : X ≠ ⊤) (hrank : 3 ≤ maxElementaryAbelianPRank ↥X) :
    ∃! M : Subgroup G, IsCoatom M ∧ X ≤ M := by
  obtain ⟨M, hM⟩ := exists_isUniqueMaximalOvergroup_of_three_le_maxElementaryAbelianPRank hna hodd
    hsolv hX hrank
  exact ⟨M, ⟨hM.isCoatom, hM.le⟩, fun N hN => hM.eq_of_isCoatom hN.1 hN.2⟩

end

end CFSG.FeitThompson
