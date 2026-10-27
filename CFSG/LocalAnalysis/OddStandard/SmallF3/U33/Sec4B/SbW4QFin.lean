module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4q5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4q7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4qC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4qD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

theorem l411_q_holds : L411QStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau hG _ hc
  have hsqO : ∀ g ∈ ctxO t tau x₁ x₂, g * g ∈ fourGrp x₁ x₂ :=
    S4B.w4q_sq_mem_V hc (S4B.w4q_lemmaF hc hG)
  have hco : ∀ a ∈ ctxO t tau x₁ x₂, ∀ b ∈ ctxO t tau x₁ x₂,
      a * b * a⁻¹ * b⁻¹ ∈ fourGrp x₁ x₂ := fun a ha b hb => S4B.w4q_comm_mem_V hc hsqO ha hb
  have hQO : ctxQ t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ :=
    S4B.w4_Q_le_O (S4B.w4q_toW4Ctxc hc).toW4Ctxa
  have hsqQ : ∀ a ∈ ctxQ t tau x₁ x₂ rho, a ^ 2 ∈ fourGrp x₁ x₂ := fun a ha => by
    rw [pow_two]
    exact hsqO a (hQO ha)
  have hCQ : ∀ x ∈ ctxQ t tau x₁ x₂ rho, x * rho = rho * x → x = 1 :=
    S4B.w4q_cent_Q_rho hc hco
  have hcard : Nat.card ↥(ctxQ t tau x₁ x₂ rho) = 2 ^ 6 := S4B.w4q_card_Q hc hco
  exact
    { toCtx4C := hc
      card_Q := hcard
      O_eq_Q := S4B.w4q_O_eq_Q hc hco
      CQ_rho := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        exact hCQ x hx.1 (Subgroup.mem_centralizer_singleton_iff.mp hx.2)
      Q_quot := ⟨hsqQ, fun a ha b hb => hco a (hQO ha) b (hQO hb)⟩
      dich := S4B.w4q_dichotomy hc hcard hCQ hsqQ }

end CFSG.OddStandard.SmallF3.HarrisU33
