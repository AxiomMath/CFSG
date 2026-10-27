
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryFixBase
import all CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryFixBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryLift

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {E : Type*} [Group E]

namespace IsUSetting

variable {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E} {β : E ≃* E}

theorem q_mem_Q8_of_fix (h : IsUSetting q l β) {e : E}
    (he : e ∈ fixT0 q β) : q e ∈ Q8 := by
  refine mem_Q8.2 ⟨?_, he.1⟩
  have h1 := h.qβ e
  rw [he.2] at h1
  calc q e * r₄ = r₄ * q e * r₄⁻¹ * r₄ := by rw [← h1]
    _ = r₄ * q e := by group

theorem card_fixT0
    [Finite E] (h : IsUSetting q l β) : Nat.card (fixT0 q β) = 8 := by
  rw [← h.card_fixed_Q8]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun e =>
    ⟨fun he => ⟨h.q_mem_Q8_of_fix he, he.2⟩, fun he => ⟨Q8_le_T0 he.1, he.2⟩⟩)

theorem mem_fixT0_of_ker
    (h : IsUSetting q l β) {z : E}
    (hz : z ∈ q.ker) : z ∈ fixT0 q β ↔ z * z = 1 := by
  rw [mem_fixT0, MonoidHom.mem_ker.mp hz, h.beta_ker hz, inv_eq_iff_mul_eq_one]
  exact and_iff_right T0.one_mem

theorem mem_K
    (h : IsUSetting q l β) (z : E) :
    z ∈ fixT0 q β ⊓ q.ker ↔ z ∈ q.ker ∧ z * z = 1 := by
  rw [mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, (h.mem_fixT0_of_ker h2).1 h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(h.mem_fixT0_of_ker h1).2 h2, h1⟩

theorem pow_four_of_ker
    (h : IsUSetting q l β) {z : E} (hz : z ∈ q.ker) :
    z ^ 4 = 1 := by
  obtain ⟨d, rfl⟩ := h.exists_psi hz
  rw [← map_pow, psi_four, map_one]

theorem beta_pp
    (h : IsUSetting q l β) (d) :
    β (l (cv (tw 35)) * l (cv (tw 35)) * psi l d) = l (cv (tw 35)) * l (cv (tw 35)) *
      psi l ((1, Multiplicative.ofAdd 3) * (1, Multiplicative.ofAdd 3) * d⁻¹) := by
  have hβp : β (l (cv (tw 35))) = l (cv (tw 35)) * psi l (1, Multiplicative.ofAdd 3) := by
    rw [← h.eps_p₁]
    group
  have hc := h.psi_comm (1, Multiplicative.ofAdd 3) (l (cv (tw 35)))
  rw [map_mul, map_mul, hβp, h.beta_psi, map_mul, map_mul]
  generalize l (cv (tw 35)) = p at hc ⊢
  generalize psi l (1, Multiplicative.ofAdd 3) = a at hc ⊢
  calc p * a * (p * a) * psi l d⁻¹ = p * (a * p) * a * psi l d⁻¹ := by group
    _ = p * (p * a) * a * psi l d⁻¹ := by rw [← hc]
    _ = p * p * (a * a * psi l d⁻¹) := by group

theorem mul_self_of_q_eq_qc
    (h : IsUSetting q l β) {e : E} (he : e ∈ fixT0 q β) (hc : q e = qc) : e * e = 1 := by
  have hpq : q (l (cv (tw 35)) * l (cv (tw 35))) = qc := by
    rw [map_mul, h.q_p₁]
    exact quat_relations.1
  have hfour := h.p₁_pow_four
  have hbeta := h.beta_pp
  have hcomm := h.psi_comm
  have hfix := he.2
  generalize l (cv (tw 35)) = p at hpq hfour hbeta
  have hw : (p * p)⁻¹ * e ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpq, hc, inv_mul_cancel]
  obtain ⟨d, hd⟩ := h.exists_psi hw
  have he' : e = p * p * psi l d := by rw [hd]; group
  rw [he', hbeta] at hfix
  have hd' := mul_left_cancel hfix
  have e2 : e * e = p ^ 4 * psi l (d * d) := by
    rw [he', map_mul, pow_four_eq]
    have hc2 := hcomm d p
    calc p * p * psi l d * (p * p * psi l d) = p * p * (psi l d * p) * p * psi l d := by group
      _ = p * p * (p * psi l d) * p * psi l d := by rw [hc2]
      _ = p * p * p * (psi l d * p) * psi l d := by group
      _ = p * p * p * (p * psi l d) * psi l d := by rw [hc2]
      _ = p * p * (p * p) * (psi l d * psi l d) := by group
  rw [e2, hfour, ← map_mul, psi_key, map_mul, hd', map_inv, mul_inv_cancel]

theorem exists_fix_qc
    (h : IsUSetting q l β) : ∃ e ∈ fixT0 q β, q e = qc := by
  have hq : q (l (cv (tw 35)) * l (cv (tw 35)) * psi l (1, Multiplicative.ofAdd 3)) = qc := by
    rw [map_mul, map_mul, h.q_p₁, h.q_psi, mul_one]
    exact quat_relations.1
  refine ⟨_, ⟨?_, ?_⟩, hq⟩
  · rw [hq]
    exact Q8_le_T0 qc_mem_Q8
  · rw [h.beta_pp, mul_inv_cancel_right]

theorem pow_four_of_fix
    (h : IsUSetting q l β) {e : E} (he : e ∈ fixT0 q β) :
    e ^ 4 = 1 := by
  have hq := h.q_mem_Q8_of_fix he
  have hee : e * e ∈ fixT0 q β := (fixT0 q β).mul_mem he he
  rw [pow_four_eq]
  rcases mul_self_mem_Q8 hq with h1 | h1
  · have hk : e * e ∈ q.ker := by rw [MonoidHom.mem_ker, map_mul]; exact h1
    exact (h.mem_fixT0_of_ker hk).1 hee
  · exact h.mul_self_of_q_eq_qc hee (by rw [map_mul]; exact h1)

theorem nonempty_fixT0_equiv
    [Finite E] (h : IsUSetting q l β) (hk : q.ker = ⊥) :
    Nonempty (fixT0 q β ≃* QuaternionGroup 2) := by
  set f : fixT0 q β →* Q8 :=
    (q.comp (fixT0 q β).subtype).codRestrict Q8 fun e => h.q_mem_Q8_of_fix e.2
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact (MonoidHom.ker_eq_bot_iff q).1 hk (congrArg Subtype.val hab)
  have hbij := hinj.bijective_of_nat_card_le (by rw [card_Q8, h.card_fixT0])
  obtain ⟨e⟩ := nonempty_Q8_equiv
  exact ⟨(MulEquiv.ofBijective f hbij).trans e⟩

end IsUSetting

end CFSG.ComponentClassification.GrSLit.L34Facts
