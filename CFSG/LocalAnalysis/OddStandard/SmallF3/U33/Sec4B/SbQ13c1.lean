module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13c_exists_conj (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∃ g : G, g * t * g⁻¹ = t * lam := by
  have ht_mem : t ∈ twoCore t := by
    rw [h.c11.l43]
    exact Subgroup.mem_zpowers t
  have hlamL : lam ∈ L := q13c_lam_mem_L h
  have hu_mem : t * lam ∈ twoCore t ⊔ L :=
    Subgroup.mul_mem_sup ht_mem hlamL
  have hu2 : (t * lam) * (t * lam) = 1 := q13c_tlam_sq h
  have hu1 : t * lam ≠ 1 := q13c_tlam_ne_one h
  obtain ⟨c0, hc0H, hcase⟩ := h.c11.invol_PL (t * lam) hu_mem hu2 hu1
  obtain ⟨-, -, hdztz⟩ := h.c11.invol_PL_distinct
  rcases hcase with h1 | h2 | h3
  · exfalso
    have hc0t : c0 * t * c0⁻¹ = t := by
      rw [S4A.mem_invCent_iff.mp hc0H]; group
    have hkey : c0 * lam * c0⁻¹ = 1 := by
      have hh : t * (c0 * lam * c0⁻¹) = t * 1 := by
        calc t * (c0 * lam * c0⁻¹) = (c0 * t * c0⁻¹) * (c0 * lam * c0⁻¹) := by rw [hc0t]
          _ = c0 * (t * lam) * c0⁻¹ := by group
          _ = t * 1 := by rw [h1, mul_one]
      exact mul_left_cancel hh
    exact q13c_lam_ne_one h (by
      calc lam = c0⁻¹ * (c0 * lam * c0⁻¹) * c0 := by group
        _ = 1 := by rw [hkey]; group)
  · exfalso
    have hlam2 : lam * lam = 1 := q13a_lam_mul_self h
    have hlam_ne : lam ≠ 1 := q13c_lam_ne_one h
    obtain ⟨c, hcL, hcz⟩ := h.c11.invol_L lam hlamL hlam2 hlam_ne
    have hcH : c ∈ invCent t := S4A.L_le_invCent h.c11.hyp hcL
    have hct : c * t = t * c := S4A.mem_invCent_iff.mp hcH
    have hcomm : t * (c * (x₁ * x₂) ^ 2 * c⁻¹) =
        c * (t * (x₁ * x₂) ^ 2) * c⁻¹ := by
      have hstep : t * (c * (x₁ * x₂) ^ 2 * c⁻¹) =
          (t * c) * (x₁ * x₂) ^ 2 * c⁻¹ := by group
      rw [hstep, ← hct]
      group
    have hu_eq : t * lam = c * (t * (x₁ * x₂) ^ 2) * c⁻¹ := by
      rw [← hcz]
      exact hcomm
    have hccH : c0 * c ∈ invCent t := (invCent t).mul_mem hc0H hcH
    have hz_eq : (c0 * c) * (t * (x₁ * x₂) ^ 2) * (c0 * c)⁻¹ = (x₁ * x₂) ^ 2 := by
      have h1 : (c0 * c) * (t * (x₁ * x₂) ^ 2) * (c0 * c)⁻¹ =
          c0 * (c * (t * (x₁ * x₂) ^ 2) * c⁻¹) * c0⁻¹ := by
        group
      rw [h1, ← hu_eq]
      exact h2
    have hconj : (c0 * c)⁻¹ * (x₁ * x₂) ^ 2 * (c0 * c) = t * (x₁ * x₂) ^ 2 := by
      have hsub : (c0 * c)⁻¹ * (x₁ * x₂) ^ 2 * (c0 * c) =
          (c0 * c)⁻¹ * ((c0 * c) * (t * (x₁ * x₂) ^ 2) * (c0 * c)⁻¹) * (c0 * c) := by
        rw [hz_eq]
      rw [hsub]
      group
    have hmem : (c0 * c)⁻¹ ∈ invCent t := (invCent t).inv_mem hccH
    exact hdztz (c0 * c)⁻¹ hmem (by simpa [inv_inv] using hconj)
  · obtain ⟨n, _hn, hnt⟩ := S4A.exists_swap_of_l42 h.c11.toCtx10.toCtx4.toCtx h.c11.l42
    refine ⟨c0⁻¹ * n, ?_⟩
    rw [show (c0⁻¹ * n) * t * (c0⁻¹ * n)⁻¹ = c0⁻¹ * (n * t * n⁻¹) * c0 by group]
    rw [hnt, ← h3]
    group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
