module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4B0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

structure Z4Pre (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Ctx4Q t L S x₁ x₂ lam rho tau where
  q_iso : IsZ4Z4E4 (ctxQ t tau x₁ x₂ rho)

namespace Z4Pre

variable (hp : Z4Pre t L S x₁ x₂ lam rho tau)
include hp

theorem Q_comm : ∀ a ∈ ctxQ t tau x₁ x₂ rho, ∀ b ∈ ctxQ t tau x₁ x₂ rho, a * b = b * a :=
  fun _ ha _ hb => S4B.IsZ4Z4E4.comm hp.q_iso ha hb

theorem Q_pow_four : ∀ a ∈ ctxQ t tau x₁ x₂ rho, a ^ 4 = 1 :=
  fun _ ha => S4B.IsZ4Z4E4.pow_four hp.q_iso ha

theorem Y_le_Q : ctxYq t tau x₁ x₂ rho ≤ ctxQ t tau x₁ x₂ rho :=
  S4B.ctxYq_le_ctxQ

theorem mem_Y_iff (a : G) : a ∈ ctxYq t tau x₁ x₂ rho ↔ a ∈ ctxQ t tau x₁ x₂ rho ∧ a ^ 2 = 1 :=
  S4B.mem_ctxYq_iff hp.q_iso a

theorem card_Y : Nat.card (ctxYq t tau x₁ x₂ rho) = 16 :=
  S4B.card_ctxYq hp.q_iso

theorem Y_comm : ∀ a ∈ ctxYq t tau x₁ x₂ rho, ∀ b ∈ ctxYq t tau x₁ x₂ rho, a * b = b * a :=
  fun _ ha _ hb => hp.Q_comm _ (hp.Y_le_Q ha) _ (hp.Y_le_Q hb)

theorem Y_sq {a : G} (ha : a ∈ ctxYq t tau x₁ x₂ rho) : a ^ 2 = 1 := ((hp.mem_Y_iff a).mp ha).2

theorem V_le_Y : fourGrp x₁ x₂ ≤ ctxYq t tau x₁ x₂ rho := by
  rw [fourGrp, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact (hp.mem_Y_iff _).mpr ⟨pow_mem hp.x₁_mem_Q 2, hp.y_sq⟩
  · exact (hp.mem_Y_iff _).mpr ⟨pow_mem (mul_mem hp.x₁_mem_Q hp.x₂_mem_Q) 2, hp.z_sq⟩

theorem Y_le_M : ctxYq t tau x₁ x₂ rho ≤ ctxM t tau x₁ x₂ := hp.Y_le_Q.trans hp.Q_le_M

theorem Y_le_O : ctxYq t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ := hp.Y_le_Q.trans hp.Q_le_O

theorem normal_Y : NormalIn (ctxYq t tau x₁ x₂ rho) (ctxM t tau x₁ x₂) := by
  refine ⟨hp.Y_le_M, fun g hg k hk => ?_⟩
  rw [hp.mem_Y_iff]
  refine ⟨hp.normal_Q.2 g hg k (hp.Y_le_Q hk), ?_⟩
  calc (g * k * g⁻¹) ^ 2 = g * k ^ 2 * g⁻¹ := conj_pow
    _ = 1 := by rw [hp.Y_sq hk]; group

theorem V_eq_sq (a : G) : a ∈ fourGrp x₁ x₂ ↔ ∃ q ∈ ctxQ t tau x₁ x₂ rho, q ^ 2 = a := by
  constructor
  · intro ha
    rw [fourGrp] at ha
    induction ha using Subgroup.closure_induction with
    | mem g hg =>
        rcases hg with hg | hg
        · exact ⟨x₁, hp.x₁_mem_Q, by rw [hg]⟩
        · exact ⟨x₁ * x₂, mul_mem hp.x₁_mem_Q hp.x₂_mem_Q, by rw [hg]⟩
    | one => exact ⟨1, one_mem _, by simp⟩
    | mul x y _ _ ihx ihy =>
        obtain ⟨q₁, hq₁, hq₁s⟩ := ihx
        obtain ⟨q₂, hq₂, hq₂s⟩ := ihy
        refine ⟨q₁ * q₂, mul_mem hq₁ hq₂, ?_⟩
        rw [Commute.mul_pow (hp.Q_comm q₁ hq₁ q₂ hq₂) 2, hq₁s, hq₂s]
    | inv x _ ihx =>
        obtain ⟨q, hq, hqs⟩ := ihx
        exact ⟨q⁻¹, inv_mem hq, by rw [inv_pow, hqs]⟩
  · rintro ⟨q, hq, rfl⟩
    exact hp.Q_quot.1 q hq

theorem sq_mem_V {q : G} (hq : q ∈ ctxQ t tau x₁ x₂ rho) : q ^ 2 ∈ fourGrp x₁ x₂ :=
  hp.Q_quot.1 q hq

end Z4Pre

end CFSG.OddStandard.SmallF3.HarrisU33
