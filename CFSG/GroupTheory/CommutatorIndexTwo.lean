module

public import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.GroupTheory

theorem commutator_eq_of_index_two_of_commutator_eq_top {G : Type*} [Group G] {N : Subgroup G}
    (hN : N.index = 2) (hperf : commutator ↥N = ⊤) : commutator G = N := by
  have : N.Normal := Subgroup.normal_of_index_eq_two hN
  have h2 : Nat.card (G ⧸ N) = 2 := by rw [← Subgroup.index_eq_card, hN]
  have hcomm : IsMulCommutative (G ⧸ N) := (isCyclic_of_prime_card h2).isMulCommutative
  refine le_antisymm (Subgroup.Normal.quotient_commutative_iff_commutator_le.1 hcomm) ?_
  calc N = (⊤ : Subgroup ↥N).map N.subtype := by rw [Subgroup.map_top, Subgroup.range_subtype]
    _ = (commutator ↥N).map N.subtype := by rw [hperf]
    _ = ⁅N, N⁆ := Subgroup.map_subtype_commutator _
    _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top

end CFSG.GroupTheory
