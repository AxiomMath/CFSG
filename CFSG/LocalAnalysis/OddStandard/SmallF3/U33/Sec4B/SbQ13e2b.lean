module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d2b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d2e

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma q13e_fix_sq (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {w g : G}
    (hw : w ∈ q13P t tau x₁ x₂ rho om)
    (hn : g * w * g⁻¹ * w⁻¹ ∈ ctxN tau x₁ x₂) :
    g * w ^ 2 * g⁻¹ = w ^ 2 := by
  have hII := hD.A_cent
  have hnP : g * w * g⁻¹ * w⁻¹ ∈ q13P t tau x₁ x₂ rho om := q13d_N_le_P h hn
  have hcomm : (g * w * g⁻¹ * w⁻¹) * w = w * (g * w * g⁻¹ * w⁻¹) :=
    q13d_P_comm h hII _ hnP w hw
  have hnn : (g * w * g⁻¹ * w⁻¹) * (g * w * g⁻¹ * w⁻¹) = 1 := by
    have h2 := (q13b_N_elemAbelian h).2 (g * w * g⁻¹ * w⁻¹) hn
    rwa [pow_two] at h2
  have hgw : g * w * g⁻¹ = (g * w * g⁻¹ * w⁻¹) * w := by group
  calc g * w ^ 2 * g⁻¹
      = (g * w * g⁻¹) ^ 2 := by rw [pow_two, pow_two]; group
    _ = ((g * w * g⁻¹ * w⁻¹) * w) ^ 2 := by conv_lhs => rw [hgw]
    _ = (g * w * g⁻¹ * w⁻¹) ^ 2 * w ^ 2 :=
          (show Commute (g * w * g⁻¹ * w⁻¹) w from hcomm).mul_pow 2
    _ = w ^ 2 := by rw [pow_two (g * w * g⁻¹ * w⁻¹), hnn, one_mul]

theorem q13e_M3 (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) {w : G}
    (hw : w ∈ q13P t tau x₁ x₂ rho om)
    (hwM : ∀ g ∈ ctxM t tau x₁ x₂, g * w * g⁻¹ * w⁻¹ ∈ ctxN tau x₁ x₂) :
    w ∈ ctxN tau x₁ x₂ := by
  have hII := hD.A_cent
  have hw2N : w ^ 2 ∈ ctxN tau x₁ x₂ := q13d_P_sq_mem_N h hII w hw
  by_contra hwN
  have hw2ne : w ^ 2 ≠ 1 := fun h1 => hwN (q13d_P_sq_eq_one_mem_N h hII w hw h1)
  rcases (q13d_mem_N h).mp hw2N with hV | ⟨v, hvV, hv_eq⟩
  · have hw2Q : w ^ 2 ∈ ctxQ t tau x₁ x₂ rho := q13a_V_le_Q h hV
    have hrhoM : rho ∈ ctxM t tau x₁ x₂ := (q13a_mem_M h).2.2.1
    have hfix := q13e_fix_sq h hD hw (hwM rho hrhoM)
    have hcomm : w ^ 2 * rho = rho * w ^ 2 := by
      calc w ^ 2 * rho = (rho * w ^ 2 * rho⁻¹) * rho := by rw [hfix]
        _ = rho * w ^ 2 := by group
    exact hw2ne (l12_cent_Q_rho h.c11 (w ^ 2) hw2Q hcomm)
  · have hx1V : x₁ ^ 2 ∈ fourGrp x₁ x₂ := (q13a_x₁_facts h).2.2.2.2.1
    have hx1ne : x₁ ^ 2 ≠ 1 := (q13a_x₁_facts h).2.2.2.2.2
    have hv''V : v * x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.mul_mem _ hvV hx1V
    have hv''ne : v * x₁ ^ 2 ≠ v := by
      intro hvv
      exact hx1ne (mul_left_cancel (a := v) (by simpa using hvv))
    have hmem1 : tau * v ∈ conjIn (ctxM t tau x₁ x₂) tau := by
      rw [h.c11.tauM]
      exact ⟨v, hvV, by change tau * v = tau * v; rfl⟩
    obtain ⟨g₁, hg₁M, hg₁⟩ := hmem1
    have hmem2 : tau * (v * x₁ ^ 2) ∈ conjIn (ctxM t tau x₁ x₂) tau := by
      rw [h.c11.tauM]
      exact ⟨v * x₁ ^ 2, hv''V, by change tau * (v * x₁ ^ 2) = tau * (v * x₁ ^ 2); rfl⟩
    obtain ⟨g₂, hg₂M, hg₂⟩ := hmem2
    have hgM : g₂ * g₁⁻¹ ∈ ctxM t tau x₁ x₂ :=
      (ctxM t tau x₁ x₂).mul_mem hg₂M ((ctxM t tau x₁ x₂).inv_mem hg₁M)
    have hfix := q13e_fix_sq h hD hw (hwM (g₂ * g₁⁻¹) hgM)
    have hconj : (g₂ * g₁⁻¹) * (tau * v) * (g₂ * g₁⁻¹)⁻¹ = tau * (v * x₁ ^ 2) := by
      rw [← hg₁, ← hg₂]
      group
    have hEq : tau * (v * x₁ ^ 2) = tau * v := by
      rw [← hconj, ← hv_eq]
      exact hfix
    exact hv''ne (mul_left_cancel hEq)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
