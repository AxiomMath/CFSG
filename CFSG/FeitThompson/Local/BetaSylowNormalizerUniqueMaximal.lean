module

public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Local.BetaNoncyclicUniqueOvergroup
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.MaximalIntersectionSylowNormalizerControl
import CFSG.FeitThompson.Local.SecondCenterPlaneCharacteristicCentralizer

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ} {X : Subgroup G}

theorem isPNarrow_of_isCyclic {Y : Type*} [Group Y] [Finite Y] (hp : p.Prime) (h : IsCyclic Y) :
    IsPNarrow p Y := by
  refine isPNarrow_of_elementaryAbelianPRank_le_two ?_
  by_contra hlt
  exact not_isCyclic_of_three_le_elementaryAbelianPRank hp (by omega) h

theorem not_isCyclic_inf_normalizer_of_mem_betaPrimes [Finite G] (hp : p ∈ betaPrimes G)
    (P : Sylow p G) (hXP : X ≤ (P : Subgroup G)) :
    ¬ IsCyclic ↥((P : Subgroup G) ⊓ normalizer (X : Set G)) := by
  have hpp : p.Prime := prime_of_mem_betaPrimes hp
  set Q : Subgroup G := (P : Subgroup G) ⊓ normalizer (X : Set G) with hQdef
  intro hcyc
  have hXQ : X ≤ Q := le_inf hXP Subgroup.le_normalizer
  have _ : IsCyclic ↥Q := hcyc
  have hkey : normalizer (Q : Set G) ⊓ (P : Subgroup G) ≤ Q :=
    le_inf inf_le_right
      (le_normalizer_of_le_of_isCyclic (A := Q) hXQ
        (K := normalizer (Q : Set G) ⊓ (P : Subgroup G)) inf_le_left)
  have hQP : Q = (P : Subgroup G) := by
    by_contra hne
    have hlt : Q < (P : Subgroup G) := lt_of_le_of_ne inf_le_left hne
    exact absurd (lt_inf_normalizer_of_lt hpp P.isPGroup' hlt) (not_lt_of_ge hkey)
  exact not_isPNarrow_of_mem_betaPrimes hp P (isPNarrow_of_isCyclic hpp (hQP ▸ hcyc))

theorem exists_isUniqueMaximalOvergroup_inf_normalizer_of_mem_betaPrimes [Finite G]
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hp : p ∈ betaPrimes G)
    (P : Sylow p G) (hXP : X ≤ (P : Subgroup G)) :
    ∃ M : Subgroup G, IsUniqueMaximalOvergroup ((P : Subgroup G) ⊓ normalizer (X : Set G)) M :=
  exists_isUniqueMaximalOvergroup_of_not_isCyclic_of_mem_betaPrimes hna hodd hsolv hp
    (P.isPGroup'.to_le inf_le_left)
    (not_isCyclic_inf_normalizer_of_mem_betaPrimes hp P hXP)

theorem existsUnique_isCoatom_ge_inf_normalizer_of_mem_betaPrimes [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hp : p ∈ betaPrimes G)
    (P : Sylow p G) (hXP : X ≤ (P : Subgroup G)) :
    ∃! M : Subgroup G, IsCoatom M ∧ (P : Subgroup G) ⊓ normalizer (X : Set G) ≤ M := by
  obtain ⟨M, hM⟩ := exists_isUniqueMaximalOvergroup_inf_normalizer_of_mem_betaPrimes
    hna hodd hsolv hp P hXP
  exact ⟨M, ⟨hM.isCoatom, hM.le⟩, fun N hN => hM.eq_of_isCoatom hN.1 hN.2⟩

end

end CFSG.FeitThompson
