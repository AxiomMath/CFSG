module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD14B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD15

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem lt_not_mem_McTT : l * t ∉ Mc ⊔ closure ({t, τ} : Set H) := by
  intro hx
  obtain ⟨m, hm, h1 | h2 | h3 | h4⟩ := (mem_McTT_iff h hMh hMc).mp hx
  · exact tl_not_mem_Mh h hMh (by rw [h.t_l, h1]; exact Mc_le_Mh h hMh hMc hm)
  · exact l_not_mem_Mh h hMh (mul_right_cancel h2 ▸ Mc_le_Mh h hMh hMc hm)
  · have hlt : l * t ∈ Mh := by
      rw [h3]
      exact Mh.mul_mem (Mc_le_Mh h hMh hMc hm) (tau_mem_Mh h hMh)
    exact tl_not_mem_Mh h hMh (by rwa [h.t_l])
  · have hl : l = m * τ := by
      calc l = l * 1 := by rw [mul_one]
        _ = l * (t * t) := by rw [h.t_sq]
        _ = (l * t) * t := by group
        _ = (m * (t * τ)) * t := by rw [h4]
        _ = m * τ := by
              have hword : (t * τ) * t = τ := by
                calc (t * τ) * t = (τ * t) * t := by rw [h.t_tau]
                  _ = τ * (t * t) := by group
                  _ = τ := by rw [h.t_sq, mul_one]
              rw [show m * (t * τ) * t = m * ((t * τ) * t) by group, hword]
    exact l_not_mem_Mh h hMh (hl ▸ Mh.mul_mem (Mc_le_Mh h hMh hMc hm) (tau_mem_Mh h hMh))

theorem V_le_commutator_Vh : V ≤ ⁅zjVh Mc t τ l, zjVh Mc t τ l⁆ := by
  have hexists : ∃ α ∈ Mc, α ∉ Q := by
    by_contra hcon
    have hle : Mc ≤ Q := fun a ha => by
      by_contra haQ
      exact hcon ⟨a, ha, haQ⟩
    have heq : Mc = Q := le_antisymm hle (Q_le_Mc h hMh hMc)
    have hcard : Nat.card Mc = Nat.card Q :=
      congrArg (fun S : Subgroup H => Nat.card ↥S) heq
    rw [card_Mc h hMh hMc, h.card_Q] at hcard
    norm_num at hcard
  intro v hv
  obtain ⟨α, hα, hαQ⟩ := hexists
  obtain ⟨u, huY, hueq⟩ := exists_conj_Y h hMh hMc hα hαQ hv
  have hv_eq : v = α⁻¹ * u * α * u⁻¹ := by
    calc v = α⁻¹ * (α * v) := by group
      _ = α⁻¹ * (u * α * u⁻¹) := by rw [← hueq]
      _ = α⁻¹ * u * α * u⁻¹ := by group
  have hv_comm : v = ⁅α⁻¹, u⁆ := by
    rw [hv_eq, commutatorElement_def, inv_inv]
  rw [hv_comm]
  exact Subgroup.commutator_mem_commutator
    (Mc_le_zjVh Mc t τ l (Mc.inv_mem hα))
    (Mc_le_zjVh Mc t τ l (Q_le_Mc h hMh hMc (h.Y_le_Q huY)))

theorem V_elem_ab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a ∧ a * a = 1 := by
  have hVY : V ≤ Y := by rw [h.Y_eq]; exact le_sup_left
  intro a ha b hb
  exact ⟨h.Q_comm a (h.Y_le_Q (hVY ha)) b (h.Y_le_Q (hVY hb)), h.Y_sq a (hVY ha)⟩

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
