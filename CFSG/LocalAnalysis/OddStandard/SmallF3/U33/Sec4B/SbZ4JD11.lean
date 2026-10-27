module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD9

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem sq_mem_Cq_all {x : H} (hx : x ∈ Mc) (hxQ : x ∉ Q)
    (hxC : x * x ∈ Q ⊓ centralizer ({t * τ} : Set H)) :
    ∀ m ∈ Mc, m * m ∈ Q ⊓ centralizer ({t * τ} : Set H) := by
  obtain ⟨D, hDmem⟩ := h.exists_sq_subgroup hMh hMc (V_le_Cq h)
  have hQMc : Q ≤ Mc := Q_le_Mc h hMh hMc
  have hQD : Q ≤ D := by
    intro q hq
    rw [hDmem q]
    exact ⟨hQMc hq, V_le_Cq h (by simpa [pow_two] using h.sq_mem_V q hq)⟩
  have hxD : x ∈ D := (hDmem x).mpr ⟨hx, hxC⟩
  have hx'Mc : ρ * x * ρ⁻¹ ∈ Mc := Mc_conj_rho h hMh hMc hx
  have hx'C : (ρ * x * ρ⁻¹) * (ρ * x * ρ⁻¹) ∈ Q ⊓ centralizer ({t * τ} : Set H) := by
    rw [show (ρ * x * ρ⁻¹) * (ρ * x * ρ⁻¹) = ρ * (x * x) * ρ⁻¹ by group]
    exact rho_norm_Cq h hxC
  have hx'D : ρ * x * ρ⁻¹ ∈ D := (hDmem _).mpr ⟨hx'Mc, hx'C⟩
  have hclosure : closure ({x, ρ * x * ρ⁻¹} : Set H) ⊔ Q ≤ D := by
    refine sup_le ?_ hQD
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hxD
    · exact hx'D
  have hMcD : Mc ≤ D := (h.Mc_le_closure hMh hMc hx hxQ).trans hclosure
  intro m hm
  exact ((hDmem m).mp (hMcD hm)).2

theorem comm_tau_mem_Cq_all {m₀ : H} (hm₀ : m₀ ∈ Mc) (hm₀Q : m₀ ∉ Q)
    (hβ : m₀ * τ * (m₀ * τ) = 1)
    (hsq : ∀ m ∈ Mc, m * m ∈ Q ⊓ centralizer ({t * τ} : Set H)) :
    ∀ m ∈ Mc, m * τ * m⁻¹ * τ⁻¹ ∈ Q ⊓ centralizer ({t * τ} : Set H) := by
  let Cq : Subgroup H := Q ⊓ centralizer ({t * τ} : Set H)
  have hconj : ∀ a ∈ Mc, ∀ c ∈ Cq, a * c * a⁻¹ ∈ Cq := by
    intro a ha c hc
    have hcQ : c ∈ Q := hc.1
    have hcomm : a * c * a⁻¹ * c⁻¹ ∈ V :=
      Mh_comm_Q h hMh (Mc_le_Mh h hMh hMc ha) hcQ
    have hcommC : a * c * a⁻¹ * c⁻¹ ∈ Cq := V_le_Cq h hcomm
    rw [show a * c * a⁻¹ = (a * c * a⁻¹ * c⁻¹) * c by group]
    exact Cq.mul_mem hcommC hc
  let D : Subgroup H :=
    { carrier := {m | m ∈ Mc ∧ m * τ * m⁻¹ * τ⁻¹ ∈ Cq}
      one_mem' := ⟨Mc.one_mem, by
        rw [show (1 : H) * τ * 1⁻¹ * τ⁻¹ = 1 by group]
        exact Cq.one_mem⟩
      mul_mem' := by
        rintro a b ⟨haMc, haC⟩ ⟨hbMc, hbC⟩
        refine ⟨Mc.mul_mem haMc hbMc, ?_⟩
        rw [show (a * b) * τ * (a * b)⁻¹ * τ⁻¹
            = (a * (b * τ * b⁻¹ * τ⁻¹) * a⁻¹) * (a * τ * a⁻¹ * τ⁻¹) by group]
        exact Cq.mul_mem (hconj a haMc _ hbC) haC
      inv_mem' := by
        rintro a ⟨haMc, haC⟩
        refine ⟨Mc.inv_mem haMc, ?_⟩
        rw [show a⁻¹ * τ * (a⁻¹)⁻¹ * τ⁻¹
            = a⁻¹ * (a * τ * a⁻¹ * τ⁻¹)⁻¹ * (a⁻¹)⁻¹ by group]
        exact hconj a⁻¹ (Mc.inv_mem haMc) _ (Cq.inv_mem haC) }
  have hDmem : ∀ m, m ∈ D ↔ m ∈ Mc ∧ m * τ * m⁻¹ * τ⁻¹ ∈ Cq := fun m => Iff.rfl
  have hQMc : Q ≤ Mc := Q_le_Mc h hMh hMc
  have hQD : Q ≤ D := by
    intro q hq
    rw [hDmem q]
    refine ⟨hQMc hq, ?_⟩
    have hτ : τ * q⁻¹ * τ⁻¹ = q := by
      rw [show τ * q⁻¹ * τ⁻¹ = (τ * q * τ⁻¹)⁻¹ by group, h.tau_inv q hq, inv_inv]
    rw [show q * τ * q⁻¹ * τ⁻¹ = q ^ 2 by
      rw [show q * τ * q⁻¹ * τ⁻¹ = q * (τ * q⁻¹ * τ⁻¹) by group, hτ, pow_two]]
    exact V_le_Cq h (h.sq_mem_V q hq)
  have hm₀D : m₀ ∈ D := by
    refine (hDmem m₀).mpr ⟨hm₀, ?_⟩
    have hτ : τ * m₀⁻¹ * τ⁻¹ = m₀ := by
      have h1 : τ * m₀ * τ = m₀⁻¹ := by
        have h2 := congrArg (fun x => m₀⁻¹ * x) hβ
        rw [mul_one] at h2
        rw [show m₀⁻¹ * (m₀ * τ * (m₀ * τ)) = τ * m₀ * τ by group] at h2
        exact h2
      have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right h.tau_sq
      calc τ * m₀⁻¹ * τ⁻¹ = τ⁻¹ * m₀⁻¹ * τ⁻¹ := by rw [hτi]
        _ = (τ * m₀ * τ)⁻¹ := by group
        _ = (m₀⁻¹)⁻¹ := by rw [h1]
        _ = m₀ := inv_inv m₀
    rw [show m₀ * τ * m₀⁻¹ * τ⁻¹ = m₀ * (τ * m₀⁻¹ * τ⁻¹) by group, hτ]
    exact hsq m₀ hm₀
  have hm₀'Mc : ρ * m₀ * ρ⁻¹ ∈ Mc := Mc_conj_rho h hMh hMc hm₀
  have hm₀'D : ρ * m₀ * ρ⁻¹ ∈ D := by
    refine (hDmem _).mpr ⟨hm₀'Mc, ?_⟩
    have hρiτ : ρ⁻¹ * τ = τ * ρ⁻¹ := by
      have h := congrArg (fun x => ρ⁻¹ * x * ρ⁻¹) h.tau_rho
      simpa [mul_assoc] using h
    have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right h.tau_sq
    have hρiτi : ρ⁻¹ * τ⁻¹ = τ⁻¹ * ρ⁻¹ := by rw [hτi, hρiτ]
    rw [show (ρ * m₀ * ρ⁻¹) * τ * (ρ * m₀ * ρ⁻¹)⁻¹ * τ⁻¹
        = ρ * (m₀ * τ * m₀⁻¹ * τ⁻¹) * ρ⁻¹ by
      calc (ρ * m₀ * ρ⁻¹) * τ * (ρ * m₀ * ρ⁻¹)⁻¹ * τ⁻¹
          = ρ * m₀ * (ρ⁻¹ * τ * ρ) * m₀⁻¹ * (ρ⁻¹ * τ⁻¹) := by group
        _ = ρ * m₀ * τ * m₀⁻¹ * (ρ⁻¹ * τ⁻¹) := by
              rw [show ρ⁻¹ * τ * ρ = τ by rw [hρiτ]; group]
        _ = ρ * m₀ * τ * m₀⁻¹ * (τ⁻¹ * ρ⁻¹) := by rw [hρiτi]
        _ = ρ * (m₀ * τ * m₀⁻¹ * τ⁻¹) * ρ⁻¹ := by group]
    exact rho_norm_Cq h (hm₀D.2)
  have hclosure : closure ({m₀, ρ * m₀ * ρ⁻¹} : Set H) ⊔ Q ≤ D := by
    refine sup_le ?_ hQD
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hm₀D
    · exact hm₀'D
  have hMcD : Mc ≤ D := (h.Mc_le_closure hMh hMc hm₀ hm₀Q).trans hclosure
  intro m hm
  exact ((hDmem m).mp (hMcD hm)).2

theorem comm_tt_mem_V
    (hcomm : ∀ m ∈ Mc, m * τ * m⁻¹ * τ⁻¹ ∈ Q ⊓ centralizer ({t * τ} : Set H)) :
    ∀ m ∈ Mc, m * (t * τ) * m⁻¹ * (t * τ)⁻¹ ∈ V := by
  intro m hm
  let w : H := m * (t * τ) * m⁻¹ * (t * τ)⁻¹
  change w ∈ V
  have hmMh : m ∈ Mh := Mc_le_Mh h hMh hMc hm
  have hss : (t * τ) * (t * τ) = 1 := by
    calc (t * τ) * (t * τ) = t * (τ * t) * τ := by group
      _ = t * (t * τ) * τ := by rw [← h.t_tau]
      _ = (t * t) * (τ * τ) := by group
      _ = 1 := by rw [h.t_sq, h.tau_sq, mul_one]
  have hsi : (t * τ)⁻¹ = t * τ := inv_eq_of_mul_eq_one_right hss
  have hCq : w ∈ Q ⊓ centralizer ({t * τ} : Set H) := by
    have h1 : w = (m * t * m⁻¹ * t⁻¹) * (t * (m * τ * m⁻¹ * τ⁻¹) * t⁻¹) := by
      simp only [w]; group
    rw [h1]
    have hmt : m * t * m⁻¹ * t⁻¹ ∈ Q ⊓ centralizer ({t * τ} : Set H) :=
      comm_t_mem_Cq h hMh hmMh
    have hmτC : m * τ * m⁻¹ * τ⁻¹ ∈ Q ⊓ centralizer ({t * τ} : Set H) := hcomm m hm
    have ht : t * (m * τ * m⁻¹ * τ⁻¹) * t⁻¹ ∈ Q ⊓ centralizer ({t * τ} : Set H) := by
      rw [inv_Cq h hmτC]
      exact (Q ⊓ centralizer ({t * τ} : Set H)).inv_mem hmτC
    exact (Q ⊓ centralizer ({t * τ} : Set H)).mul_mem hmt ht
  have hwQ : w ∈ Q := hCq.1
  have hcommw : w * (t * τ) = (t * τ) * w :=
    Subgroup.mem_centralizer_singleton_iff.mp hCq.2
  have hconj : (t * τ) * w * (t * τ)⁻¹ = w := by
    calc (t * τ) * w * (t * τ)⁻¹ = (w * (t * τ)) * (t * τ)⁻¹ := by rw [hcommw]
      _ = w := by group
  have hwx : w = m * (t * τ) * m⁻¹ * (t * τ) := by simp only [w, hsi]
  have hinv : w⁻¹ = (t * τ) * m * (t * τ) * m⁻¹ := by
    rw [hwx]
    have h2 : (m * (t * τ) * m⁻¹ * (t * τ))⁻¹
        = (t * τ)⁻¹ * m * (t * τ)⁻¹ * m⁻¹ := by group
    rw [h2, hsi]
  have hconj2 : (t * τ) * w * (t * τ)⁻¹ = (t * τ) * m * (t * τ) * m⁻¹ := by
    simp only [w]
    rw [show (t * τ) * (m * (t * τ) * m⁻¹ * (t * τ)⁻¹) * (t * τ)⁻¹
        = (t * τ) * m * (t * τ) * m⁻¹ * ((t * τ)⁻¹ * (t * τ)⁻¹) by group]
    rw [show (t * τ)⁻¹ * (t * τ)⁻¹ = 1 by rw [hsi, hss]]
    group
  have hw_eq_inv : w = w⁻¹ := by
    calc w = (t * τ) * w * (t * τ)⁻¹ := hconj.symm
      _ = (t * τ) * m * (t * τ) * m⁻¹ := hconj2
      _ = w⁻¹ := hinv.symm
  have hsq : w * w = 1 :=
    (congrArg (fun x => w * x) hw_eq_inv).trans (mul_inv_cancel w)
  have hwY : w ∈ Y := h.Y_mem w hwQ hsq
  have htw : t * w = w * t := by
    have h1 : t * w * t⁻¹ = w⁻¹ := inv_Cq h hCq
    have h2 : w⁻¹ = w := inv_eq_of_mul_eq_one_right hsq
    calc t * w = (t * w * t⁻¹) * t := by group
      _ = w⁻¹ * t := by rw [h1]
      _ = w * t := by rw [h2]
  exact h.Y_cent_t w hwY htw

theorem card_cent_tt_ge (hV : ∀ m ∈ Mc, m * (t * τ) * m⁻¹ * (t * τ)⁻¹ ∈ V) :
    64 ≤ Nat.card ↥(Mc ⊓ centralizer ({t * τ} : Set H)) := by
  have hG₀ : ∀ m ∈ Mc, ∀ v ∈ V, m * v * m⁻¹ = v :=
    fun m hm v hv => Mh_cent_V h hMh (Mc_le_Mh h hMh hMc hm) hv
  obtain ⟨D, hDmem, hDcard⟩ := h.exists_comm_subgroup hG₀ (t * τ)
  have hDMc : D = Mc := by
    apply le_antisymm
    · intro m hm
      exact ((hDmem m).mp hm).1
    · intro m hm
      exact (hDmem m).mpr ⟨hm, hV m hm⟩
  have hcardD : Nat.card D = 256 := by
    rw [hDMc]
    exact card_Mc h hMh hMc
  rw [hcardD] at hDcard
  omega

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
