module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5k
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5l0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem conj_t_cases (ha : Ctx4P t L S x₁ x₂ lam rho tau) {B : Subgroup G} {ω : G}
    (hB : BData t x₁ x₂ lam rho tau B ω) :
    ∀ p ∈ ctxPL t tau x₁ x₂, ∃ b ∈ B, p * t * p⁻¹ = b * t ∨ p * t * p⁻¹ = b * ω * t := by
  intro p hp
  have hl := ha.toCtx4L
  have hc := hl.toCtx4Q
  let w : G := p * t * p⁻¹
  let u : G := w * t⁻¹
  have hwO : w ∈ ctxO t tau x₁ x₂ :=
    (Subgroup.mem_normalizer_iff.mp (P_le_LO ha hp) t).mp hc.t_mem_O
  have hu : u ∈ ctxO t tau x₁ x₂ :=
    (ctxO t tau x₁ x₂).mul_mem hwO ((ctxO t tau x₁ x₂).inv_mem hc.t_mem_O)
  have ht2 : t * t = 1 := T_sq hc t (Subgroup.subset_closure (Set.mem_insert t {tau}))
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hact : ∀ b ∈ (B : Set G), w * b * w⁻¹ = t * b * t⁻¹ :=
    conj_act_eq (fourGrp x₁ x₂) (B : Set G) p t (V_sq hc) (P_comm_V ha p hp)
      (fun v hv => V_comm_O hc hc.t_mem_O hv)
      (fun b hb => hB.P_comm b hb p hp)
      (fun b hb => O_comm_le hc hc.t_mem_O (hc.Q_le_O (hB.le_Q hb)))
  have hu_eq : u = w * t := by
    show w * t⁻¹ = w * t
    rw [ht_inv]
  have hcent : ∀ b ∈ B, u * b = b * u := by
    intro b hb
    have hV : t * b * t⁻¹ * b⁻¹ ∈ fourGrp x₁ x₂ :=
      O_comm_le hc hc.t_mem_O (hc.Q_le_O (hB.le_Q hb))
    have hb' : t * b * t⁻¹ ∈ B := by
      have hm := B.mul_mem (hB.V_le hV) hb
      rwa [show t * b * t⁻¹ * b⁻¹ * b = t * b * t⁻¹ by group] at hm
    have h1 : w * (t * b * t⁻¹) * w⁻¹ = b := by
      have h1' := hact (t * b * t⁻¹) hb'
      have htb : t * (t * b * t⁻¹) * t⁻¹ = b := by
        rw [ht_inv]
        calc t * (t * b * t) * t = (t * t) * b * (t * t) := by group
          _ = b := by rw [ht2]; group
      rwa [htb] at h1'
    have h2 : w * (t * b * t⁻¹) = b * w := by
      have hw := congrArg (· * w) h1
      rwa [mul_assoc, inv_mul_cancel, mul_one] at hw
    have h3 : w * (t * b * t) = b * w := by
      rwa [ht_inv] at h2
    have h2' : w * t * b * t = b * w := by
      rw [show w * t * b * t = w * (t * b * t) by group]
      exact h3
    have h4 : w * t * b = b * w * t := by
      calc w * t * b = (w * t * b) * (t * t) := by simp only [ht2, mul_one]
        _ = ((w * t * b) * t) * t := by group
        _ = (b * w) * t := congrArg (· * t) h2'
        _ = b * w * t := by group
    calc u * b = w * t * b := by rw [hu_eq]
      _ = b * w * t := h4
      _ = b * (w * t) := by group
      _ = b * u := by rw [hu_eq]
  obtain ⟨b, hb, h⟩ := cent_decomp ha hB u hu hcent
  refine ⟨b, hb, ?_⟩
  have hwu : w = u * t := by
    show w = (w * t⁻¹) * t
    group
  rcases h with h | h
  · left
    change w = b * t
    rw [hwu, h]
  · right
    change w = b * ω * t
    rw [hwu, h]

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
