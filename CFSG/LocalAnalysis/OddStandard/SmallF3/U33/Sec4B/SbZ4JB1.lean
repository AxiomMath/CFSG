module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JA1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

namespace ZJBase

variable (h : ZJBase Q Y V V' B ρ t τ l y z v₁ v₂)
include h

private theorem V_le_Y : V ≤ Y := by
  rw [h.Y_eq]
  exact le_sup_left

private theorem V'_le_Y : V' ≤ Y := by
  rw [h.Y_eq]
  exact le_sup_right

private theorem Y_comm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a :=
  fun a ha b hb => h.Q_comm a (h.Y_le_Q ha) b (h.Y_le_Q hb)

private theorem Y_inv_self {u : H} (hu : u ∈ Y) : u⁻¹ = u :=
  inv_eq_of_mul_eq_one_right (h.Y_sq u hu)

private theorem conj_eq_self {e u : H} (he : e ∈ centralizer (Y : Set H)) (hu : u ∈ Y) :
    e * u * e⁻¹ = u := by
  have hcomm : u * e = e * u := (mem_centralizer_iff.1 he) u hu
  rw [← hcomm]
  group

theorem Q_le_E : Q ≤ centralizer (Y : Set H) := by
  intro q hq
  rw [mem_centralizer_iff]
  intro u hu
  exact h.Q_comm u (h.Y_le_Q hu) q hq

theorem E_normal {g e : H} (he : e ∈ centralizer (Y : Set H)) :
    g * e * g⁻¹ ∈ centralizer (Y : Set H) := by
  rw [mem_centralizer_iff] at he ⊢
  intro u hu
  have hu' : g⁻¹ * u * g ∈ Y := by
    have := h.normal_Y g⁻¹ u hu
    simpa using this
  have hc : (g⁻¹ * u * g) * e = e * (g⁻¹ * u * g) := he _ hu'
  calc u * (g * e * g⁻¹) = (g * (g⁻¹ * u * g) * g⁻¹) * (g * e * g⁻¹) := by group
    _ = g * ((g⁻¹ * u * g) * e) * g⁻¹ := by group
    _ = g * (e * (g⁻¹ * u * g)) * g⁻¹ := by rw [hc]
    _ = (g * e * g⁻¹) * u := by group

theorem E_comm_mem_Y {e q : H} (he : e ∈ centralizer (Y : Set H)) (hq : q ∈ Q) :
    e * q * e⁻¹ * q⁻¹ ∈ Y := by
  have ha : e * q * e⁻¹ ∈ Q := h.normal_Q e q hq
  have hwQ : e * q * e⁻¹ * q⁻¹ ∈ Q := Q.mul_mem ha (Q.inv_mem hq)
  apply h.Y_mem _ hwQ
  have hqq : q * q ∈ Y := by
    simpa only [pow_two] using h.V_le_Y (h.sq_mem_V q hq)
  have hcomm : (q * q) * e = e * (q * q) := (mem_centralizer_iff.1 he) (q * q) hqq
  have haa : (e * q * e⁻¹) * (e * q * e⁻¹) = q * q := by
    calc (e * q * e⁻¹) * (e * q * e⁻¹) = e * (q * q) * e⁻¹ := by group
      _ = q * q := by rw [← hcomm]; group
  have hqa : q⁻¹ * (e * q * e⁻¹) = (e * q * e⁻¹) * q⁻¹ :=
    h.Q_comm q⁻¹ (Q.inv_mem hq) (e * q * e⁻¹) ha
  calc (e * q * e⁻¹ * q⁻¹) * (e * q * e⁻¹ * q⁻¹)
      = (e * q * e⁻¹) * (q⁻¹ * (e * q * e⁻¹)) * q⁻¹ := by group
    _ = (e * q * e⁻¹) * ((e * q * e⁻¹) * q⁻¹) * q⁻¹ := by rw [hqa]
    _ = ((e * q * e⁻¹) * (e * q * e⁻¹)) * (q⁻¹ * q⁻¹) := by group
    _ = (q * q) * (q⁻¹ * q⁻¹) := by rw [haa]
    _ = 1 := by group

theorem E_sq_mem_Q {e : H} (he : e ∈ centralizer (Y : Set H)) : e * e ∈ Q := by
  refine h.cent_Q (e * e) fun q hq => ?_
  set w : H := e * q * e⁻¹ * q⁻¹ with hwdef
  have hw : w ∈ Y := by rw [hwdef]; exact h.E_comm_mem_Y he hq
  have hwq : e * q * e⁻¹ = w * q := by rw [hwdef]; group
  have hcw : e * w * e⁻¹ = w := h.conj_eq_self he hw
  have hww : w * w = 1 := h.Y_sq w hw
  have hkey : (e * e) * q * (e * e)⁻¹ = q := by
    calc (e * e) * q * (e * e)⁻¹ = e * (e * q * e⁻¹) * e⁻¹ := by group
      _ = e * (w * q) * e⁻¹ := by rw [hwq]
      _ = (e * w * e⁻¹) * (e * q * e⁻¹) := by group
      _ = w * (w * q) := by rw [hcw, hwq]
      _ = (w * w) * q := by group
      _ = q := by rw [hww, one_mul]
  calc (e * e) * q = ((e * e) * q * (e * e)⁻¹) * (e * e) := by group
    _ = q * (e * e) := by rw [hkey]

theorem E_pow_eight {e : H} (he : e ∈ centralizer (Y : Set H)) : e ^ 8 = 1 := by
  have haQ : e * e ∈ Q := h.E_sq_mem_Q he
  have haY : (e * e) ^ 2 ∈ Y := h.V_le_Y (h.sq_mem_V (e * e) haQ)
  have h1 : (e * e) ^ 2 * (e * e) ^ 2 = 1 := h.Y_sq _ haY
  have hpow : e ^ 8 = (e * e) ^ 2 * (e * e) ^ 2 := by
    calc e ^ 8 = (e ^ 2) ^ 4 := by rw [show (8 : ℕ) = 2 * 4 by norm_num, ← pow_mul]
      _ = (e ^ 2) ^ 2 * (e ^ 2) ^ 2 := by
        rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
      _ = (e * e) ^ 2 * (e * e) ^ 2 := by simp only [pow_two]
  exact hpow.trans h1

theorem E_comm_mem_Q {e e' : H} (he : e ∈ centralizer (Y : Set H))
    (he' : e' ∈ centralizer (Y : Set H)) : e * e' * e⁻¹ * e'⁻¹ ∈ Q := by
  have hsame : ∀ q ∈ Q,
      (e * e') * q * (e * e')⁻¹ = (e' * e) * q * (e' * e)⁻¹ := by
    intro q hq
    set w : H := e * q * e⁻¹ * q⁻¹ with hwdef
    set w' : H := e' * q * e'⁻¹ * q⁻¹ with hw'def
    have hw : w ∈ Y := by rw [hwdef]; exact h.E_comm_mem_Y he hq
    have hw' : w' ∈ Y := by rw [hw'def]; exact h.E_comm_mem_Y he' hq
    have hwq : e * q * e⁻¹ = w * q := by rw [hwdef]; group
    have hw'q : e' * q * e'⁻¹ = w' * q := by rw [hw'def]; group
    have hce : e * w' * e⁻¹ = w' := h.conj_eq_self he hw'
    have hce' : e' * w * e'⁻¹ = w := h.conj_eq_self he' hw
    have hcommY : w * w' = w' * w := h.Y_comm _ hw _ hw'
    have h1 : (e * e') * q * (e * e')⁻¹ = (w' * w) * q := by
      calc (e * e') * q * (e * e')⁻¹ = e * (e' * q * e'⁻¹) * e⁻¹ := by group
        _ = e * (w' * q) * e⁻¹ := by rw [hw'q]
        _ = (e * w' * e⁻¹) * (e * q * e⁻¹) := by group
        _ = w' * (w * q) := by rw [hce, hwq]
        _ = (w' * w) * q := by group
    have h2 : (e' * e) * q * (e' * e)⁻¹ = (w' * w) * q := by
      calc (e' * e) * q * (e' * e)⁻¹ = e' * (e * q * e⁻¹) * e'⁻¹ := by group
        _ = e' * (w * q) * e'⁻¹ := by rw [hwq]
        _ = (e' * w * e'⁻¹) * (e' * q * e'⁻¹) := by group
        _ = w * (w' * q) := by rw [hce', hw'q]
        _ = (w * w') * q := by group
        _ = (w' * w) * q := by rw [hcommY]
    exact h1.trans h2.symm
  refine h.cent_Q (e * e' * e⁻¹ * e'⁻¹) fun q hq => ?_
  have hq' : (e' * e)⁻¹ * q * (e' * e) ∈ Q := by
    simpa using h.normal_Q (e' * e)⁻¹ q hq
  have hkey : (e * e' * e⁻¹ * e'⁻¹) * q * (e * e' * e⁻¹ * e'⁻¹)⁻¹ = q := by
    calc (e * e' * e⁻¹ * e'⁻¹) * q * (e * e' * e⁻¹ * e'⁻¹)⁻¹
        = (e * e') * ((e' * e)⁻¹ * q * (e' * e)) * (e * e')⁻¹ := by group
      _ = (e' * e) * ((e' * e)⁻¹ * q * (e' * e)) * (e' * e)⁻¹ := hsame _ hq'
      _ = q := by group
  calc (e * e' * e⁻¹ * e'⁻¹) * q
      = ((e * e' * e⁻¹ * e'⁻¹) * q * (e * e' * e⁻¹ * e'⁻¹)⁻¹) * (e * e' * e⁻¹ * e'⁻¹) := by
        group
    _ = q * (e * e' * e⁻¹ * e'⁻¹) := by rw [hkey]

theorem E_isPGroup : IsPGroup 2 (centralizer (Y : Set H)) := by
  intro g
  refine ⟨3, ?_⟩
  apply Subtype.ext
  simpa using h.E_pow_eight g.2

theorem tau_mem_E : τ ∈ centralizer (Y : Set H) := by
  rw [mem_centralizer_iff]
  intro u hu
  have htau : τ * u * τ⁻¹ = u := by
    rw [h.tau_inv u (h.Y_le_Q hu), h.Y_inv_self hu]
  calc u * τ = (τ * u * τ⁻¹) * τ := by rw [htau]
    _ = τ * u := by group

theorem t_not_mem_E : t ∉ centralizer (Y : Set H) := by
  intro ht
  have hv₁V' : v₁ ∈ V' := by
    rw [h.V'_eq]
    exact Subgroup.subset_closure (by simp)
  have hv₁Y : v₁ ∈ Y := h.V'_le_Y hv₁V'
  have hcomm : v₁ * t = t * v₁ := (mem_centralizer_iff.1 ht) v₁ hv₁Y
  have h1 : t * v₁ * t⁻¹ = v₁ := by rw [← hcomm]; group
  have hy : v₁ * y = v₁ := by rw [← h.t_v₁, h1]
  exact h.y_ne_one (mul_left_cancel (by rw [hy, mul_one]))

theorem tt_not_mem_E : t * τ ∉ centralizer (Y : Set H) := by
  intro ht
  apply h.t_not_mem_E
  have hτ : τ ∈ centralizer (Y : Set H) := h.tau_mem_E
  have hmem : (t * τ) * τ⁻¹ ∈ centralizer (Y : Set H) :=
    Subgroup.mul_mem _ ht (Subgroup.inv_mem _ hτ)
  have heq : (t * τ) * τ⁻¹ = t := by group
  rwa [heq] at hmem

end ZJBase

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
