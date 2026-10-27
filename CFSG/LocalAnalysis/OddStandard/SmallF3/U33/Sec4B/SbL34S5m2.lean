module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5g1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5l

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped Pointwise
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem case_elem (ha : Ctx4P t L S x₁ x₂ lam rho tau) {B : Subgroup G} {ω : G}
    (hB : BData t x₁ x₂ lam rho tau B ω) (hω : ω ≠ t) (hE : ∀ b ∈ B, b * b = 1) : False := by
  have hc := ha.toCtx4L.toCtx4Q
  have hl := ha.toCtx4L
  have hωT : ω = tau ∨ ω = t * tau := by
    rcases (mem_T_iff hc).mp hB.ω_mem with h | h | h | h
    · exact absurd h hB.ω_ne
    · exact absurd h hω
    · exact Or.inl h
    · exact Or.inr h
  have hω2 : ω * ω = 1 := T_sq hc ω hB.ω_mem
  have hωt : ω * t = t * ω :=
    T_comm hc ω hB.ω_mem t (Subgroup.subset_closure (by simp))
  have ht2 : t * t = 1 := T_sq hc t (Subgroup.subset_closure (by simp))
  have hVleN : fourGrp x₁ x₂ ≤ ctxN (t * tau) x₁ x₂ := by
    rw [fourGrp, ctxN]
    exact Subgroup.closure_mono (by intro a ha; simp at ha ⊢; tauto)
  have hVleNtau : fourGrp x₁ x₂ ≤ ctxN tau x₁ x₂ := by
    rw [fourGrp, ctxN]
    exact Subgroup.closure_mono (by intro a ha; simp at ha ⊢; tauto)
  have hkey : ∀ b ∈ B, (b * t) * (b * t) = 1 → b ∈ fourGrp x₁ x₂ := by
    intro b hb hbt2
    have hb2 : b * b = 1 := hE b hb
    have hbt : b * t = t * b := by
      have hinv : (b * t)⁻¹ = b * t := inv_eq_of_mul_eq_one_right hbt2
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2, inv_eq_of_mul_eq_one_right hb2] at hinv
      exact hinv.symm
    have hbtau : b * tau = tau * b := by
      rcases hωT with h | h
      · have hcω := hB.ω_comm b hb
        rw [h] at hcω
        exact hcω.symm
      · have htau_eq : tau = t * ω := by
          rw [h]
          rw [show t * (t * tau) = tau by
            calc t * (t * tau) = (t * t) * tau := by rw [← mul_assoc]
              _ = tau := by rw [ht2, one_mul]]
        rw [htau_eq]
        calc b * (t * ω) = (b * t) * ω := by rw [← mul_assoc]
          _ = (t * b) * ω := by rw [hbt]
          _ = t * (b * ω) := by rw [mul_assoc]
          _ = t * (ω * b) := by rw [hB.ω_comm b hb]
          _ = (t * ω) * b := by rw [← mul_assoc]
    exact mem_V_of_comm_T ha (hB.le_Q hb) hbt hbtau
  refine false_of_conj_tV ha ?_
  intro p hp
  have hw : (p * t * p⁻¹) * (p * t * p⁻¹) = 1 := by
    rw [show (p * t * p⁻¹) * (p * t * p⁻¹) = p * (t * t) * p⁻¹ by group]
    rw [ht2, mul_one, mul_inv_cancel]
  obtain ⟨b, hb, h | h⟩ := conj_t_cases ha hB p hp
  · have hbt2 : (b * t) * (b * t) = 1 := by rw [← h]; exact hw
    have hbV : b ∈ fourGrp x₁ x₂ := hkey b hb hbt2
    have hbt : b * t = t * b := (V_comm_O hc hc.t_mem_O hbV).symm
    have hp_eq : p * t * p⁻¹ = t * b := by rw [h, hbt]
    rw [hp_eq]
    exact Set.mem_smul_set.mpr ⟨b, hbV, rfl⟩
  · have hbωt_eq : b * ω * t = (b * t) * ω := by
      calc b * ω * t = b * (ω * t) := by rw [mul_assoc]
        _ = b * (t * ω) := by rw [hωt]
        _ = (b * t) * ω := by rw [← mul_assoc]
    have hcomm : (b * t) * ω = ω * (b * t) := by
      calc (b * t) * ω = b * (t * ω) := by rw [← mul_assoc]
        _ = b * (ω * t) := by rw [← hωt]
        _ = (b * ω) * t := by rw [mul_assoc]
        _ = (ω * b) * t := by rw [← hB.ω_comm b hb]
        _ = ω * (b * t) := by rw [mul_assoc]
    have hbt2 : (b * t) * (b * t) = 1 := by
      have h1 : (b * ω * t) * (b * ω * t) = 1 := by rw [← h]; exact hw
      have hsq : (b * ω * t) * (b * ω * t) = ((b * t) * (b * t)) * (ω * ω) := by
        rw [hbωt_eq]
        rw [show ((b * t) * ω) * ((b * t) * ω) = (b * t) * (ω * ((b * t) * ω)) by group]
        rw [show ω * ((b * t) * ω) = (ω * (b * t)) * ω by group]
        rw [← hcomm]
        group
      rw [hsq, hω2, mul_one] at h1
      exact h1
    have hbV : b ∈ fourGrp x₁ x₂ := hkey b hb hbt2
    rcases hωT with hωtau | hωttau
    · have hmem : b * tau * t ∈ ctxN (t * tau) x₁ x₂ := by
        have hbN : b ∈ ctxN (t * tau) x₁ x₂ := hVleN hbV
        have hgen : t * tau ∈ ctxN (t * tau) x₁ x₂ := Subgroup.subset_closure (by simp)
        have heq : b * tau * t = b * (t * tau) := by rw [mul_assoc, ← hc.t_comm_tau]
        rw [heq]
        exact (ctxN (t * tau) x₁ x₂).mul_mem hbN hgen
      rw [hωtau] at h
      exact absurd h (hl.tG_tN p (b * tau * t) hmem)
    · have httaut : (t * tau) * t = tau := by
        calc (t * tau) * t = t * (tau * t) := by rw [mul_assoc]
          _ = t * (t * tau) := by rw [← hc.t_comm_tau]
          _ = (t * t) * tau := by rw [← mul_assoc]
          _ = tau := by rw [ht2, one_mul]
      have heq : b * (t * tau) * t = b * tau := by
        rw [mul_assoc, httaut]
      have hmem : b * tau ∈ ctxN tau x₁ x₂ := by
        have hbN : b ∈ ctxN tau x₁ x₂ := hVleNtau hbV
        exact (ctxN tau x₁ x₂).mul_mem hbN (Subgroup.subset_closure (by simp))
      rw [hωttau] at h
      rw [heq] at h
      exact absurd h (hl.tG_N p (b * tau) hmem)

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
