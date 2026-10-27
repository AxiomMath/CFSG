module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLate9CEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII


open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20G.late_swap_not_N_member (d : Std20G K K' J S R R' W V z t) {σ m a₀ : G}
    (hσ : σ ∈ (S : Subgroup G)) (hσK : conjSub σ K = K') (hσa : σ * a₀ * σ⁻¹ = a₀)
    (hme : m * z * m⁻¹ = a₀) (ha₀ : a₀ = z ∨ a₀ = t ∨ a₀ = z * t) {L : Subgroup G}
    (hL : L = conjSub m K ∨ L = conjSub m K') (hσL : conjSub σ L = L) : False := by
  obtain ⟨hL₁, hL₂, hL₁₂, hL₁i, hL₂i⟩ := d.late_member_data m
  rw [hme] at hL₁i hL₂i
  obtain ⟨hK'σ, -, -, -⟩ := d.late_swap_data hσ hσK
  have hperm : ∀ L' : Subgroup G, L' ∈ CoreAssembly.conjClass K → IsUniqueInvolution L' a₀ →
      conjSub σ L' = conjSub m K ∨ conjSub σ L' = conjSub m K' := by
    intro L' hL' hL'i
    have hLi' : IsUniqueInvolution (conjSub σ L') a₀ := by
      have := hL'i.conj σ
      rwa [hσa] at this
    exact d.late_members_of_inv hme (d.hyp.conjInvariant σ L' hL') hLi'
  have hboth : conjSub σ (conjSub m K) = conjSub m K ∧ conjSub σ (conjSub m K') = conjSub m K' := by
    rcases hL with rfl | rfl
    · refine ⟨hσL, ?_⟩
      rcases hperm _ hL₂ hL₂i with h' | h'
      · exact absurd (conjSub_injective σ (hσL.trans h'.symm)) hL₁₂
      · exact h'
    · refine ⟨?_, hσL⟩
      rcases hperm _ hL₁ hL₁i with h' | h'
      · exact h'
      · exact absurd (conjSub_injective σ (h'.trans hσL.symm)) hL₁₂
  rcases ha₀ with h | h | h
  ·
    have hK₁ := d.late_members_of_inv (m := 1) (e := z) (by group) hL₁
      (by rw [← h]; exact hL₁i)
    rcases hK₁ with h1 | h1
    · rw [conjSub_one] at h1
      have := hboth.1
      rw [h1] at this
      exact d.ne (hσK.symm.trans this)
    · rw [conjSub_one] at h1
      have := hboth.1
      rw [h1, hK'σ] at this
      exact d.ne this.symm
  ·
    have hσt : σ * t * σ⁻¹ = t := by rw [← h]; exact hσa
    have hJ' : IsUniqueInvolution J a₀ := by rw [h]; exact d.viol.hzJ
    have hJc : conjSub σ J = J := by
      rcases d.late_members_of_inv hme d.late_mem_J hJ' with h1 | h1
      · rw [h1]
        exact hboth.1
      · rw [h1]
        exact hboth.2
    exact d.late_swap_J hσ hσK hσt (Subgroup.one_mem _) (by simpa using hJc)
  ·
    have hσt : σ * t * σ⁻¹ = t := by
      rcases d.late_S_act_t hσ with h' | h'
      · exact h'
      · exfalso
        have : σ * (z * t) * σ⁻¹ = z * (z * t) := by
          calc σ * (z * t) * σ⁻¹ = (σ * z * σ⁻¹) * (σ * t * σ⁻¹) := by group
            _ = z * (z * t) := by rw [d.late_S_act_z hσ, h']
        rw [h, this] at hσa
        have h3 : z * t = t := by
          calc z * t = z * (z * t) := hσa.symm
            _ = t := by rw [← mul_assoc, d.viol.hzK.sq, one_mul]
        exact d.viol.hzK.ne_one (by simpa using h3)
    obtain ⟨r, hr, r', hr', -, hrt⟩ := d.late_tor d.late_JW d.late_hW
    have hJ' := d.viol.hzJ.conj r
    rw [hrt, ← h] at hJ'
    have hJc : conjSub σ (conjSub r J) = conjSub r J := by
      rcases d.late_members_of_inv hme (d.hyp.conjInvariant r J d.late_mem_J) hJ' with h1 | h1
      · rw [h1]
        exact hboth.1
      · rw [h1]
        exact hboth.2
    exact d.late_swap_J hσ hσK hσt hr hJc

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
