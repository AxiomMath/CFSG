module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5g1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5o
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5l
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped Pointwise
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem case_t (ha : Ctx4P t L S x₁ x₂ lam rho tau) {B : Subgroup G} {ω : G}
    (hB : BData t x₁ x₂ lam rho tau B ω) (hω : ω = t) : False := by
  have hl := ha.toCtx4L
  have hc := hl.toCtx4Q
  have hBbase : B = baseGrp x₁ x₂ := by
    rw [B_eq_CQ ha hB, hω, CQ_t_eq_base hc]
  have hx1B : x₁ ∈ B := by
    rw [hBbase, baseGrp]
    exact Subgroup.subset_closure (by simp)
  have hx1sq : x₁ * x₁ ≠ 1 := by
    rw [← pow_two]
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hc.wreath.ord_x₁]; norm_num)
  have hΩ : ∀ b ∈ B, b * b = 1 → b ∈ fourGrp x₁ x₂ := by
    rcases omega_cases_B ha hB with hE | hΩ'
    · exact absurd (hE x₁ hx1B) hx1sq
    · exact hΩ'
  have ht2 : t * t = 1 := T_sq hc t (Subgroup.subset_closure (Set.mem_insert t {tau}))
  have htB : ∀ b ∈ B, t * b = b * t := by
    intro b hb
    rw [← hω]
    exact hB.ω_comm b hb
  apply false_of_conj_tV ha
  intro p hp
  obtain ⟨b, hb, h | h⟩ := conj_t_cases ha hB p hp
  ·
    rw [h]
    have hw : (p * t * p⁻¹) * (p * t * p⁻¹) = 1 := by
      rw [show (p * t * p⁻¹) * (p * t * p⁻¹) = p * (t * t) * p⁻¹ by group, ht2]
      group
    rw [h] at hw
    have hbb : b * b = 1 := by
      have hbt : (b * t) * (b * t) = b * b := by
        calc (b * t) * (b * t) = b * (t * b) * t := by group
          _ = b * (b * t) * t := by rw [htB b hb]
          _ = (b * b) * (t * t) := by group
          _ = b * b := by rw [ht2, mul_one]
      rw [← hbt]
      exact hw
    refine Set.mem_smul_set.mpr ⟨b, hΩ b hb hbb, ?_⟩
    show t * b = b * t
    rw [htB b hb]
  ·
    rw [hω] at h
    have hw : (p * t * p⁻¹) * (p * t * p⁻¹) = 1 := by
      rw [show (p * t * p⁻¹) * (p * t * p⁻¹) = p * (t * t) * p⁻¹ by group, ht2]
      group
    have hb_eq : p * t * p⁻¹ = b := by
      rw [h, mul_assoc, ht2, mul_one]
    have hbb : b * b = 1 := by
      rw [← hb_eq]
      exact hw
    have hbV : b ∈ fourGrp x₁ x₂ := hΩ b hb hbb
    have hbp : p⁻¹ * b * p = b := by
      have hpb : p * b = b * p := P_comm_V ha p hp b hbV
      rw [mul_assoc, ← hpb, ← mul_assoc, inv_mul_cancel, one_mul]
    have hpt : p * t * p⁻¹ = t := by
      have ht_eq : t = p⁻¹ * b * p := by
        have h1 : p⁻¹ * (p * t * p⁻¹) * p = t := by group
        rw [hb_eq] at h1
        exact h1.symm
      rw [hb_eq]
      exact (ht_eq.trans hbp).symm
    rw [hpt]
    refine Set.mem_smul_set.mpr ⟨1, (fourGrp x₁ x₂).one_mem, ?_⟩
    simp

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
