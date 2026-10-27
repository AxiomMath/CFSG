module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4B0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4Stmt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQab

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z

theorem Q_comm (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    ∀ a ∈ ctxQ t tau x₁ x₂ rho, ∀ b ∈ ctxQ t tau x₁ x₂ rho, a * b = b * a :=
  fun _ ha _ hb => S4B.IsZ4Z4E4.comm hz.q_iso ha hb

theorem Q_pow_four (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    ∀ a ∈ ctxQ t tau x₁ x₂ rho, a ^ 4 = 1 :=
  fun _ ha => S4B.IsZ4Z4E4.pow_four hz.q_iso ha

theorem Y_le_Q (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    ctxYq t tau x₁ x₂ rho ≤ ctxQ t tau x₁ x₂ rho :=
  S4B.ctxYq_le_ctxQ

theorem mem_Y_iff (hz : Ctx4Z t L S x₁ x₂ lam rho tau) (a : G) :
    a ∈ ctxYq t tau x₁ x₂ rho ↔ a ∈ ctxQ t tau x₁ x₂ rho ∧ a ^ 2 = 1 :=
  S4B.mem_ctxYq_iff hz.q_iso a

theorem card_Y (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    Nat.card (ctxYq t tau x₁ x₂ rho) = 16 :=
  S4B.card_ctxYq hz.q_iso

theorem Y_isElemAbelian (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    CFSG.Open.IsElemAbelian 2 (ctxYq t tau x₁ x₂ rho) := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro a b
    exact Subtype.ext (hz.Q_comm a.1 (Y_le_Q hz a.2) b.1 (Y_le_Q hz b.2))
  · intro x hx
    exact ((mem_Y_iff hz x).mp hx).2

theorem V_le_Y (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    fourGrp x₁ x₂ ≤ ctxYq t tau x₁ x₂ rho := by
  rw [fourGrp, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact (mem_Y_iff hz (x₁ ^ 2)).mpr ⟨pow_mem hz.toCtx4Q.x₁_mem_Q 2, hz.toCtx4Q.y_sq⟩
  · exact (mem_Y_iff hz ((x₁ * x₂) ^ 2)).mpr
      ⟨pow_mem (mul_mem hz.toCtx4Q.x₁_mem_Q hz.toCtx4Q.x₂_mem_Q) 2, hz.toCtx4Q.z_sq⟩

theorem V_eq_sq (hz : Ctx4Z t L S x₁ x₂ lam rho tau) (a : G) :
    a ∈ fourGrp x₁ x₂ ↔ ∃ q ∈ ctxQ t tau x₁ x₂ rho, q ^ 2 = a := by
  constructor
  · intro ha
    rw [fourGrp] at ha
    induction ha using Subgroup.closure_induction with
    | mem g hg =>
        rcases hg with hg | hg
        · exact ⟨x₁, hz.toCtx4Q.x₁_mem_Q, by rw [hg]⟩
        · exact ⟨x₁ * x₂, mul_mem hz.toCtx4Q.x₁_mem_Q hz.toCtx4Q.x₂_mem_Q, by rw [hg]⟩
    | one => exact ⟨1, one_mem _, by simp⟩
    | mul x y _ _ ihx ihy =>
        obtain ⟨q₁, hq₁, hq₁s⟩ := ihx
        obtain ⟨q₂, hq₂, hq₂s⟩ := ihy
        refine ⟨q₁ * q₂, mul_mem hq₁ hq₂, ?_⟩
        rw [Commute.mul_pow (hz.Q_comm q₁ hq₁ q₂ hq₂) 2, hq₁s, hq₂s]
    | inv x _ ihx =>
        obtain ⟨q, hq, hqs⟩ := ihx
        exact ⟨q⁻¹, inv_mem hq, by rw [inv_pow, hqs]⟩
  · rintro ⟨q, hq, rfl⟩
    exact hz.Q_quot.1 q hq

theorem normal_Y (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    NormalIn (ctxYq t tau x₁ x₂ rho) (ctxM t tau x₁ x₂) := by
  refine ⟨(Y_le_Q hz).trans hz.toCtx4Q.Q_le_M, ?_⟩
  intro g hg k hk
  rw [mem_Y_iff hz]
  have hk2 : k ^ 2 = 1 := ((mem_Y_iff hz k).mp hk).2
  refine ⟨hz.normal_Q.2 g hg k (Y_le_Q hz hk), ?_⟩
  calc (g * k * g⁻¹) ^ 2 = g * k ^ 2 * g⁻¹ := conj_pow
    _ = g * 1 * g⁻¹ := by rw [hk2]
    _ = 1 := by group

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
