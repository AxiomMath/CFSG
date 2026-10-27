module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem relIndex_sup_of_le_normalizer {N K : Subgroup G} (hK : K ≤ normalizer (N : Set G)) :
    N.relIndex (K ⊔ N) = N.relIndex K := by
  have hNA : N ≤ normalizer (N : Set G) := Subgroup.le_normalizer
  haveI : (N.subgroupOf (normalizer (N : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mpr le_rfl
  have h := Subgroup.relIndex_sup_right (H := K.subgroupOf (normalizer (N : Set G)))
    (K := N.subgroupOf (normalizer (N : Set G)))
  rw [← Subgroup.subgroupOf_sup hK hNA, Subgroup.relIndex_subgroupOf (sup_le hK hNA),
    Subgroup.relIndex_subgroupOf hK] at h
  exact h

theorem card_sup_mul_card_inf_of_le_normalizer {N K : Subgroup G}
    (hK : K ≤ normalizer (N : Set G)) :
    Nat.card ↥(N ⊔ K) * Nat.card ↥(N ⊓ K) = Nat.card N * Nat.card K := by
  have h1 := Subgroup.relIndex_mul_card N (K ⊔ N)
  have h2 := Subgroup.relIndex_mul_card N K
  rw [inf_eq_left.mpr (le_sup_right : N ≤ K ⊔ N), relIndex_sup_of_le_normalizer hK,
    sup_comm] at h1
  rw [← h1, ← h2]
  ring

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
