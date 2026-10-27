module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IS1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IS1A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Prod

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H]

namespace ZIKData

variable {Q Y V V' B K : Subgroup H} {ρ : H}

theorem V_le_Y (h : ZIKData Q Y V V' B K ρ) : V ≤ Y := by
  rw [h.Y_eq]
  exact le_sup_left

theorem V'_le_Y (h : ZIKData Q Y V V' B K ρ) : V' ≤ Y := by
  rw [h.Y_eq]
  exact le_sup_right

theorem V_le_Q (h : ZIKData Q Y V V' B K ρ) : V ≤ Q :=
  h.V_le_Y.trans h.Y_le_Q

theorem V'_le_Q (h : ZIKData Q Y V V' B K ρ) : V' ≤ Q :=
  h.V'_le_Y.trans h.Y_le_Q

theorem Y_comm (h : ZIKData Q Y V V' B K ρ) : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a :=
  fun a ha b hb => h.Q_comm a (h.Y_le_Q ha) b (h.Y_le_Q hb)

theorem card_Y (h : ZIKData Q Y V V' B K ρ) : Nat.card Y = 16 := by
  have hnorm : ∀ k ∈ V', ∀ v ∈ V, k * v * k⁻¹ ∈ V := by
    intro k hk v hv
    rw [h.Q_comm k (h.V'_le_Q hk) v (h.V_le_Q hv), mul_assoc, mul_inv_cancel, mul_one]
    exact hv
  have hcard := card_sup_eq_mul (H := V) (K := V') hnorm h.V_inf_V'
  rw [h.Y_eq, hcard, h.card_V, h.card_V']

theorem card_K (h : ZIKData Q Y V V' B K ρ) : Nat.card K = 256 := by
  have hinf : Q ⊓ K = Q := inf_of_le_left h.Q_le_K
  have hcard := relIndex_mul_card (H := Q) (K := K)
  rw [hinf, h.relIndex_K, h.card_Q] at hcard
  omega

theorem relIndex_YQ (h : ZIKData Q Y V V' B K ρ) : Y.relIndex Q = 4 := by
  have hinf : Y ⊓ Q = Y := inf_of_le_left h.Y_le_Q
  have hcard := relIndex_mul_card (H := Y) (K := Q)
  rw [hinf, h.card_Y, h.card_Q] at hcard
  omega

theorem Q_normal_K (h : ZIKData Q Y V V' B K ρ) :
    ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q := by
  intro k hk q hq
  have hmem : k * q * k⁻¹ * q⁻¹ ∈ V := h.comm_KQ k hk q hq
  rw [show k * q * k⁻¹ = (k * q * k⁻¹ * q⁻¹) * q by group]
  exact Q.mul_mem (h.V_le_Q hmem) hq

theorem exists_mul_BY (h : ZIKData Q Y V V' B K ρ) :
    ∀ q ∈ Q, ∃ b ∈ B, ∃ y ∈ Y, q = b * y := by
  intro q hq
  have hnorm : ∀ k ∈ V', ∀ b ∈ B, k * b * k⁻¹ ∈ B := by
    intro k hk b hb
    rw [h.Q_comm k (h.V'_le_Q hk) b (h.B_le_Q hb), mul_assoc, mul_inv_cancel, mul_one]
    exact hb
  have hq' : q ∈ B ⊔ V' := by rwa [← h.Q_eq]
  obtain ⟨b, hb, v, hv, hqv⟩ := (mem_sup_iff_of_normalizes (H := B) (K := V') hnorm).mp hq'
  exact ⟨b, hb, v, h.V'_le_Y hv, hqv⟩

theorem fpf_QY (h : ZIKData Q Y V V' B K ρ) :
    ∀ q ∈ Q, ρ * q * ρ⁻¹ * q⁻¹ ∈ Y → q ∈ Y := by
  intro q hq hy
  exact z4i_fpf_quot (Q := Q) (N := Y) h.Y_le_Q h.Q_comm h.rho_norm_Y h.rho_fpf_Q hq hy

theorem fpf_KY (h : ZIKData Q Y V V' B K ρ) :
    ∀ k ∈ K, ρ * k * ρ⁻¹ * k⁻¹ ∈ Y → k ∈ Y := by
  intro k hk hy
  exact h.fpf_QY k (h.rho_fpf_KQ k hk (h.Y_le_Q hy)) hy

theorem fpf_YV (h : ZIKData Q Y V V' B K ρ) :
    ∀ y ∈ Y, ρ * y * ρ⁻¹ * y⁻¹ ∈ V → y ∈ V := by
  intro y hy hyv
  exact z4i_fpf_quot (Q := Y) (N := V) h.V_le_Y h.Y_comm h.rho_norm_V
    (fun z hz hzfix => h.rho_fpf_Q z (h.Y_le_Q hz) hzfix) hy hyv

theorem K_sq_mem_Q (h : ZIKData Q Y V V' B K ρ) : ∀ k ∈ K, k ^ 2 ∈ Q := by
  intro k hk
  exact z4i_sq_mem_of_relIndex_four (N := Q) (M := K) h.rho_pow_three h.Q_le_K h.Q_normal_K
    h.rho_norm_Q h.rho_norm_K h.relIndex_K h.rho_fpf_KQ hk

theorem comm_eq_one_of_mem_Y (h : ZIKData Q Y V V' B K ρ) {x y : H} (hx : x ∈ K)
    (hy : y ∈ Y) : ⁅x, y⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (h.K_cent_Y x hx y hy)

theorem comm_mul_right (h : ZIKData Q Y V V' B K ρ) {x q q' : H} (hx : x ∈ K) (hq : q ∈ Q)
    (hq' : q' ∈ Q) : ⁅x, q * q'⁆ = ⁅x, q⁆ * ⁅x, q'⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hmem : ⁅x, q'⁆ ∈ Q := h.V_le_Q (h.comm_KQ x hx q' hq')
  have hconj : q * ⁅x, q'⁆ * q⁻¹ = ⁅x, q'⁆ := by
    rw [h.Q_comm q hq ⁅x, q'⁆ hmem]
    group
  rw [show ⁅x, q⁆ * q * ⁅x, q'⁆ * q⁻¹ = ⁅x, q⁆ * (q * ⁅x, q'⁆ * q⁻¹) by group, hconj]

theorem comm_mul_left (h : ZIKData Q Y V V' B K ρ) {x x' q : H} (hx : x ∈ K) (hx' : x' ∈ K)
    (hq : q ∈ Q) : ⁅x * x', q⁆ = ⁅x', q⁆ * ⁅x, q⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hmem : ⁅x', q⁆ ∈ Y := h.V_le_Y (h.comm_KQ x' hx' q hq)
  have hconj : x * ⁅x', q⁆ * x⁻¹ = ⁅x', q⁆ := by
    rw [h.K_cent_Y x hx ⁅x', q⁆ hmem]
    group
  rw [show x * ⁅x', q⁆ * x⁻¹ * ⁅x, q⁆ = (x * ⁅x', q⁆ * x⁻¹) * ⁅x, q⁆ by group, hconj]

end ZIKData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
