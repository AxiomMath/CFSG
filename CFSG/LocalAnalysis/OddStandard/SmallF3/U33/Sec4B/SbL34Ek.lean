module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Ek1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5g0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34 CFSG.OddStandard.SmallF3.HarrisU33.L34Z

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem card_LO_eq_six_mul_card_PL (ha : Ctx4A t L S x₁ x₂ lam rho tau) :
    Nat.card (ctxLO t tau x₁ x₂) = 6 * Nat.card (ctxPL t tau x₁ x₂) := by
  have hl := ha.toCtx4L
  have hc := hl.toCtx4Q
  have hs := isSylSL34_of_Ctx4L hl
  have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := subset_closure (by simp)
  have hσ : t * lam ∈ ctxLO t tau x₁ x₂ := by
    rw [t_comm_lam hc]
    exact lamt_mem_LO ha
  refine card_eq_six_mul_card_centralizer (ctxLO t tau x₁ x₂) (fourGrp x₁ x₂)
    (fun g hg v hv => conj_V_of_mem_LO hc hs hg hv) (card_fourGrp hc)
    (fun a ha' b hb' => V_comm_Q hc a ha' b (hc.V_le_Q hb')) (V_sq hc)
    (rho_mem_LO ha) hσ (rho_cubed hc) (q_mul_self hc) ?_ ?_
  · intro v hv hfix
    refine rho_fix_Q hc v (hc.V_le_Q hv) ?_
    calc rho * v = (rho * v * rho⁻¹) * rho := by group
      _ = v * rho := by rw [hfix]
  · refine ⟨x₁ ^ 2, hyV, fun h => z_ne_one hc ?_⟩
    rw [q_conj_y hc] at h
    simpa using h

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
