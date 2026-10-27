module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Model28

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Equiv Subgroup

theorem D28_le_K28 (b : Bool) : D28 ≤ K28 b := by
  unfold D28 K28
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  exact hx.elim Or.inl (fun h => Or.inr (Or.inl h))

theorem pT_commute_of_mem_K28 (b : Bool) : ∀ k ∈ K28 b, k * pT = pT * k := by
  have hA : pA * pT = pT * pA := by
    simp only [pA, pT, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hB : pB * pT = pT * pB := by
    simp only [pB, pT, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hG : pG b * pT = pT * pG b := by
    have ht : (if b then hTwo else hOne) * tFour = tFour * (if b then hTwo else hOne) := by
      cases b <;> decide
    simp only [pG, pT, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, ht]
  intro k hk
  have hle : K28 b ≤ Subgroup.centralizer ({pT} : Set (Perm (Fin 28))) := by
    unfold K28
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hA
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hB
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hG
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hk)

end CFSG.EvenSporadicStandard.M12Std.PropA
