module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RHarada

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem uA_not_mem {G : Type} [Group G] {z σ c d : G} {V0 : Subgroup G}
    (hz2 : z * z = 1) (hσ2 : σ * σ = 1)
    (hV0z : V0 ≤ Subgroup.centralizer ({z} : Set G))
    (hcV0 : c ∈ V0) (hdV0 : d ∈ V0) (hσV0 : σ ∉ V0)
    (hzV0 : z ∉ V0 ⊔ Subgroup.zpowers σ) :
    z * σ ∉ Subgroup.closure ({z, c, d} : Set G) := by
  intro hmem
  have hle : Subgroup.closure ({z, c, d} : Set G) ≤ Subgroup.zpowers z ⊔ V0 := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    · rw [h]; exact mem_sup_left (Subgroup.mem_zpowers _)
    · rw [h]; exact mem_sup_right hcV0
    · rw [h]; exact mem_sup_right hdV0
  have hx : z * σ ∈ V0 ⊔ Subgroup.zpowers z := by
    rw [sup_comm]
    exact hle hmem
  have hzc : z ∈ Subgroup.centralizer (V0 : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun v hv => mem_centralizer_singleton_iff.1 (hV0z hv)
  obtain ⟨v, hv, w, hw, hvw⟩ := exists_mul_of_mem_sup_comm' (Subgroup.zpowers_le.2 hzc) hx
  rcases mem_zpowers_sq_eq_one hz2 hw with h | h
  ·
    rw [h, mul_one] at hvw
    have hzeq : z = v * σ := by
      calc z = z * (σ * σ) := by rw [hσ2, mul_one]
        _ = z * σ * σ := by rw [mul_assoc]
        _ = v * σ := by rw [hvw]
    apply hzV0
    rw [hzeq]
    exact mul_mem (mem_sup_left hv) (mem_sup_right (Subgroup.mem_zpowers σ))
  ·
    rw [h] at hvw
    have hvz : v * z = z * v := mem_centralizer_singleton_iff.1 (hV0z hv)
    rw [hvz] at hvw
    have hσv : σ = v := mul_left_cancel hvw
    exact hσV0 (by rw [hσv]; exact hv)

end CFSG.EvenSporadicStandard.Fin76b
