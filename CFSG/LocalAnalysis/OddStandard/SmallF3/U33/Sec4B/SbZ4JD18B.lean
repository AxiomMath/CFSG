module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD13
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD16

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem tau_comm_Y {u : H} (hu : u ∈ Y) : τ * u = u * τ := by
  have hτ : τ ∈ centralizer (Y : Set H) := by
    rw [h.E_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)
  exact ((Subgroup.mem_centralizer_iff.mp hτ) u hu).symm

theorem cent_Y_eq_V {α : H} (hα : α ∈ Mc) (hαQ : α ∉ Q) {u : H} (hu : u ∈ Y)
    (hc : u * α = α * u) : u ∈ V := by
  have hαMh : α ∈ Mh := Mc_le_Mh h hMh hMc hα
  have hαE : α ∉ centralizer (Y : Set H) := fun hcY =>
    hαQ (mem_Q_of_mem_Mc_cent_Y h hMh hMc hα hcY)
  exact Mh_cent_Y h hMh hαMh hαE hu (by rw [← hc]; group)

theorem no_inv_Mct (hb : ZJBound t)
    (hK : ∀ x ∈ Mc, x ∉ Q → x * x ∉ Q ⊓ centralizer ({t * τ} : Set H))
    {T : H → Prop} (hT : ZJClass T Q t τ l) {m₀ : H} (hm₀ : m₀ ∈ Mc)
    (hβ : m₀ * τ * (m₀ * τ) = 1) (hTβ : T (m₀ * τ)) {m : H} (hm : m ∈ Mc)
    (hd2 : m * t * (m * t) = 1) (hdβ : m₀ * τ * (m * t) = m * t * (m₀ * τ)) : False := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
  have h2 : t * m * (t * m) = 1 := by
    calc t * m * (t * m) = t * (m * t * (m * t)) * t⁻¹ := by group
      _ = t * 1 * t⁻¹ := by rw [hd2]
      _ = 1 := by rw [mul_one, hti, h.t_sq]
  obtain ⟨w, hw, hwe⟩ := Il_t h hMh hMc hb hK hm h2
  let g : H := t * w
  have hg_t : g * t * g⁻¹ = m * t := by
    have hh := hwe
    calc g * t * g⁻¹ = t * (w * t * w⁻¹) * t⁻¹ := by
          rw [show g = t * w from rfl]; group
      _ = t * (t * m) * t⁻¹ := by rw [hh]
      _ = m * t := by
            rw [hti]
            calc t * (t * m) * t = (t * t) * m * t := by group
              _ = m * t := by rw [h.t_sq]; group
  have hg_inv_t : g⁻¹ * (m * t) * g = t := by
    have h := congrArg (fun x => g⁻¹ * x * g) hg_t
    rw [show g⁻¹ * (g * t * g⁻¹) * g = t by group] at h
    exact h.symm
  have hcomm_conj : (g⁻¹ * (m₀ * τ) * g) * t = t * (g⁻¹ * (m₀ * τ) * g) := by
    have h := congrArg (fun x => g⁻¹ * x * g) hdβ
    have hL : g⁻¹ * (m₀ * τ * (m * t)) * g =
        (g⁻¹ * (m₀ * τ) * g) * (g⁻¹ * (m * t) * g) := by group
    have hR : g⁻¹ * ((m * t) * (m₀ * τ)) * g =
        (g⁻¹ * (m * t) * g) * (g⁻¹ * (m₀ * τ) * g) := by group
    rw [hL, hR, hg_inv_t] at h
    exact h
  let m' : H := w⁻¹ * (t * m₀ * t⁻¹) * (τ * w * τ)
  have hm' : m' ∈ Mc := by
    have hτw : τ * w * τ ∈ Mc := by
      have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right h.tau_sq
      simpa [hτi] using Mc_conj_tau h hMh hMc hw
    exact Mc.mul_mem (Mc.mul_mem (Mc.inv_mem hw)
      (Mc_conj_t h hMh hMc hm₀)) hτw
  have hβ'eq : g⁻¹ * (m₀ * τ) * g = m' * τ := by
    have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right h.tau_sq
    have hτt : τ * t = t * τ := h.t_tau.symm
    have hginv : g⁻¹ = w⁻¹ * t := by rw [show g = t * w from rfl, mul_inv_rev, hti]
    have hm'def : m' = w⁻¹ * (t * m₀ * t⁻¹) * (τ * w * τ) := rfl
    have hτcancel : (τ * w * τ) * τ = τ * w := by
      calc (τ * w * τ) * τ = τ * w * (τ * τ) := by group
        _ = τ * w := by rw [h.tau_sq, mul_one]
    rw [hginv, hm'def]
    calc (w⁻¹ * t) * (m₀ * τ) * (t * w)
        = w⁻¹ * t * m₀ * (τ * t) * w := by group
      _ = w⁻¹ * t * m₀ * (t * τ) * w := by rw [hτt]
      _ = w⁻¹ * (t * m₀ * t⁻¹) * (τ * w) := by
            rw [hti]
            group
      _ = w⁻¹ * (t * m₀ * t⁻¹) * ((τ * w * τ) * τ) := by rw [hτcancel]
      _ = w⁻¹ * (t * m₀ * t⁻¹) * (τ * w * τ) * τ := by group
  have hTβ' : T (g⁻¹ * (m₀ * τ) * g) := by
    have h := hT.conj (m₀ * τ) g⁻¹ hTβ
    simpa using h
  have hm't : t * m' = m' * t := by
    have hh := hcomm_conj
    rw [hβ'eq] at hh
    have h' : m' * t * τ = t * m' * τ := by
      calc m' * t * τ = m' * (t * τ) := by group
        _ = m' * (τ * t) := by rw [h.t_tau]
        _ = m' * τ * t := by group
        _ = t * (m' * τ) := hh
        _ = t * m' * τ := by group
    exact (mul_right_cancel h').symm
  have hm'B : m' ∈ B := Mc_cent_t h hMh hMc hb hm' hm't
  have hm'Q : m' ∈ Q := h.B_le_Q hm'B
  rw [hβ'eq] at hTβ'
  exact (hT.not_Qtau m' hm'Q) hTβ'

theorem no_inv_Mctau_t (hb : ZJBound t)
    (hK : ∀ x ∈ Mc, x ∉ Q → x * x ∉ Q ⊓ centralizer ({t * τ} : Set H))
    {T : H → Prop} (hT : ZJClass T Q t τ l) {m₀ : H} (hm₀ : m₀ ∈ Mc)
    (hβ : m₀ * τ * (m₀ * τ) = 1) (hTβ : T (m₀ * τ)) {m : H} (hm : m ∈ Mc)
    (hd2 : m * (t * τ) * (m * (t * τ)) = 1)
    (hdβ : m₀ * τ * (m * (t * τ)) = m * (t * τ) * (m₀ * τ)) : False := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
  have hτm₀ : τ * m₀ * τ = m₀⁻¹ := by
    have h := congrArg (fun y => m₀⁻¹ * y) hβ
    simpa [mul_assoc] using h
  let m'' : H := m * (t * m₀⁻¹ * t⁻¹)
  have hd_eq : m * (t * τ) * (m₀ * τ) = m'' * t := by
    have hlhs : m * (t * τ) * (m₀ * τ) = m * t * (τ * m₀ * τ) := by group
    have hr : m'' * t = m * t * m₀⁻¹ := by
      rw [show m'' = m * (t * m₀⁻¹ * t⁻¹) from rfl, hti]
      calc m * (t * m₀⁻¹ * t) * t = (m * t * m₀⁻¹) * (t * t) := by group
        _ = m * t * m₀⁻¹ := by rw [h.t_sq, mul_one]
    rw [hlhs, hτm₀, hr]
  have hm'' : m'' ∈ Mc := by
    rw [show m'' = m * (t * m₀⁻¹ * t⁻¹) from rfl]
    exact Mc.mul_mem hm (Mc_conj_t h hMh hMc (Mc.inv_mem hm₀))
  have hd2d : (m * (t * τ) * (m₀ * τ)) * (m * (t * τ) * (m₀ * τ)) = 1 := by
    have hcomm : m * (t * τ) * (m₀ * τ) = (m₀ * τ) * (m * (t * τ)) := hdβ.symm
    calc (m * (t * τ) * (m₀ * τ)) * (m * (t * τ) * (m₀ * τ))
        = (m * (t * τ)) * ((m₀ * τ) * (m * (t * τ))) * (m₀ * τ) := by group
      _ = (m * (t * τ)) * ((m * (t * τ)) * (m₀ * τ)) * (m₀ * τ) := by rw [← hcomm]
      _ = ((m * (t * τ)) * (m * (t * τ))) * ((m₀ * τ) * (m₀ * τ)) := by group
      _ = 1 := by rw [hd2, hβ, one_mul]
  have hd2'' : m'' * t * (m'' * t) = 1 := by
    rw [← hd_eq]
    exact hd2d
  have hdβ'' : m₀ * τ * (m'' * t) = (m'' * t) * (m₀ * τ) := by
    rw [← hd_eq]
    calc (m₀ * τ) * (m * (t * τ) * (m₀ * τ))
        = ((m₀ * τ) * (m * (t * τ))) * (m₀ * τ) := by group
      _ = ((m * (t * τ)) * (m₀ * τ)) * (m₀ * τ) := by rw [hdβ]
      _ = (m * (t * τ) * (m₀ * τ)) * (m₀ * τ) := by group
  exact no_inv_Mct h hMh hMc hb hK hT hm₀ hβ hTβ hm'' hd2'' hdβ''

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
