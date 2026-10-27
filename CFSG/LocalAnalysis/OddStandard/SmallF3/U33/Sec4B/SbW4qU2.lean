module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbM4Stmt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4q_card_le_two_inf {U O F : Subgroup G} (hFU : F ≤ U) (hOU : O ≤ U)
    (hidx : Nat.card U = 2 * Nat.card O) : Nat.card F ≤ 2 * Nat.card ↥(F ⊓ O) := by
  have hrelOU : O.relIndex U = 2 := by
    have h := Subgroup.relIndex_mul_card (H := O) (K := U)
    rw [inf_eq_left.mpr hOU, hidx] at h
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥O)) h
  have hcard : Nat.card F = (F ⊓ O).relIndex F * Nat.card ↥(F ⊓ O) := by
    have h := Subgroup.relIndex_mul_card (H := F ⊓ O) (K := F)
    rw [inf_of_le_left inf_le_left] at h
    exact h.symm
  have hle : O.relIndex F ≤ O.relIndex U :=
    Subgroup.relIndex_le_of_le_right hFU (by rw [hrelOU]; norm_num)
  rw [hcard, Subgroup.inf_relIndex_left]
  exact Nat.mul_le_mul_right _ (by rw [← hrelOU]; exact hle)

theorem w4q_mem_O_of_not_mem {U O : Subgroup G} (hOU : O ≤ U)
    (hidx : Nat.card U = 2 * Nat.card O) {g h : G} (hg : g ∈ U) (hgO : g ∉ O) (hh : h ∈ U)
    (hhO : h ∉ O) : g⁻¹ * h ∈ O := by
  have hrelOU : O.relIndex U = 2 := by
    have h := Subgroup.relIndex_mul_card (H := O) (K := U)
    rw [inf_eq_left.mpr hOU, hidx] at h
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥O)) h
  have hH : (O.subgroupOf U).index = 2 := hrelOU
  have hmem : (⟨g⁻¹, inv_mem hg⟩ : U) * ⟨h, hh⟩ ∈ O.subgroupOf U := by
    refine (Subgroup.mul_mem_iff_of_index_two (H := O.subgroupOf U) hH).mpr ?_
    exact iff_of_false
      (fun hg' => hgO (by simpa using O.inv_mem (Subgroup.mem_subgroupOf.mp hg')))
      (fun hh' => hhO (Subgroup.mem_subgroupOf.mp hh'))
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

theorem w4q_lam_y_ne (hc : Ctx4C t L S x₁ x₂ lam rho tau) : lam * x₁ ^ 2 * lam⁻¹ ≠ x₁ ^ 2 := by
  have hw : WreathRel x₁ x₂ lam := hc.wreath
  intro hfix
  have hconj : lam * x₁ ^ 2 * lam⁻¹ = x₂ ^ 2 := by
    rw [← conj_pow (a := lam) (b := x₁) (i := 2), hw.conj_x₁]
  have hz : (x₁ * x₂) ^ 2 = 1 := by
    have h : x₁ ^ 2 * (x₁ * x₂) ^ 2 = x₁ ^ 2 := by
      rw [← hw.x₂_sq]
      exact hconj.symm.trans hfix
    exact mul_left_cancel (h.trans (mul_one _).symm)
  have hx2sq : x₂ ^ 2 = x₁ ^ 2 := by rw [hw.x₂_sq, hz, mul_one]
  have hmem : x₁ ^ 2 ∈ zpowers x₁ ⊓ zpowers x₂ :=
    ⟨pow_mem (Subgroup.mem_zpowers x₁) 2,
      by rw [← hx2sq]; exact pow_mem (Subgroup.mem_zpowers x₂) 2⟩
  rw [hw.inf_eq_bot, Subgroup.mem_bot] at hmem
  exact (pow_ne_one_of_lt_orderOf (by norm_num : (2 : ℕ) ≠ 0)
    (by rw [hw.ord_x₁]; norm_num)) hmem

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
