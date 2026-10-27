module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD4

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

private theorem zj_comm_swap {G : Type*} [Group G] (n m : G) : ⁅n, m⁆ = ⁅m, n⁆⁻¹ := by
  rw [← inv_inv ⁅n, m⁆, commutatorElement_inv]

private theorem zj_mul_inv {G : Type*} [Group G] (A B : G) : B * A⁻¹ = (A * B⁻¹)⁻¹ := by
  rw [mul_inv_rev, inv_inv]

private theorem comm_rho_identity' {G : Type*} [Group G] (r m : G) :
    ⁅m, r * m * r⁻¹⁆ * ⁅r * m * r⁻¹, r⁻¹ * m * r⁆⁻¹
      = ⁅m * (r * m * r⁻¹), ⁅r * m * r⁻¹, r⁻¹ * m * r⁆⁆
        * (⁅r * m * r⁻¹, r⁻¹ * m * r⁆
            * ⁅m * (r * m * r⁻¹) * (r⁻¹ * m * r), r * m * r⁻¹⁆
            * ⁅r * m * r⁻¹, r⁻¹ * m * r⁆⁻¹) := by
  group

private theorem conj_comm_rho_identity {G : Type*} [Group G] (r m : G)
    (h : r * (r * m * r⁻¹) * r⁻¹ = r⁻¹ * m * r) :
    r * ⁅m, r * m * r⁻¹⁆ * r⁻¹ = ⁅r * m * r⁻¹, r⁻¹ * m * r⁆ := by
  have h1 : r * ⁅m, r * m * r⁻¹⁆ * r⁻¹
      = ⁅r * m * r⁻¹, r * (r * m * r⁻¹) * r⁻¹⁆ := by
    group
  rw [h1, h]

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

private theorem V_le_Y_of_data : V ≤ Y := by rw [h.Y_eq]; exact le_sup_left

private theorem V_le_Q_of_data : V ≤ Q := fun x hx => h.Y_le_Q (h.V_le_Y_of_data hx)

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem Mc_comm_rho_mem_V {m : H} (hm : m ∈ Mc) :
    m * (ρ * m * ρ⁻¹) * m⁻¹ * (ρ * m * ρ⁻¹)⁻¹ ∈ V := by
  have hρ2 : ρ * ρ = ρ⁻¹ := by
    have h3 := h.rho_pow_three
    rw [pow_three] at h3
    exact eq_inv_of_mul_eq_one_right h3
  have heq : ρ * (ρ * m * ρ⁻¹) * ρ⁻¹ = ρ⁻¹ * m * ρ := by
    have h1 : ρ * (ρ * m * ρ⁻¹) * ρ⁻¹ = (ρ * ρ) * m * (ρ * ρ)⁻¹ := by group
    rw [h1, hρ2, inv_inv]
  have hm' : ρ * m * ρ⁻¹ ∈ Mc := h.Mc_conj_rho hMh hMc hm
  have hm'' : ρ⁻¹ * m * ρ ∈ Mc := by
    rw [← heq]
    exact h.Mc_conj_rho hMh hMc hm'
  have hmMh : m ∈ Mh := h.Mc_le_Mh hMh hMc hm
  have hm'Mh : ρ * m * ρ⁻¹ ∈ Mh := h.Mc_le_Mh hMh hMc hm'
  have hm''Mh : ρ⁻¹ * m * ρ ∈ Mh := h.Mc_le_Mh hMh hMc hm''
  have hnQ : m * (ρ * m * ρ⁻¹) * (ρ⁻¹ * m * ρ) ∈ Q := by
    have h1 := ((hMc m).mp hm).2
    rwa [zjNorm] at h1
  have hBQ : ⁅ρ * m * ρ⁻¹, ρ⁻¹ * m * ρ⁆ ∈ Q := h.Mh_comm_mem_Q hMh hm'Mh hm''Mh
  have hnm'V : ⁅m * (ρ * m * ρ⁻¹) * (ρ⁻¹ * m * ρ), ρ * m * ρ⁻¹⁆ ∈ V := by
    have h1 : ⁅ρ * m * ρ⁻¹, m * (ρ * m * ρ⁻¹) * (ρ⁻¹ * m * ρ)⁆ ∈ V :=
      h.Mh_comm_Q hMh hm'Mh hnQ
    rw [zj_comm_swap]
    exact V.inv_mem h1
  have hcBV : ⁅m * (ρ * m * ρ⁻¹), ⁅ρ * m * ρ⁻¹, ρ⁻¹ * m * ρ⁆⁆ ∈ V :=
    h.Mh_comm_Q hMh (Mh.mul_mem hmMh hm'Mh) hBQ
  have hB_comm : ⁅ρ * m * ρ⁻¹, ρ⁻¹ * m * ρ⁆
      * ⁅m * (ρ * m * ρ⁻¹) * (ρ⁻¹ * m * ρ), ρ * m * ρ⁻¹⁆
      * ⁅ρ * m * ρ⁻¹, ρ⁻¹ * m * ρ⁆⁻¹
      = ⁅m * (ρ * m * ρ⁻¹) * (ρ⁻¹ * m * ρ), ρ * m * ρ⁻¹⁆ := by
    have hXQ : ⁅m * (ρ * m * ρ⁻¹) * (ρ⁻¹ * m * ρ), ρ * m * ρ⁻¹⁆ ∈ Q :=
      h.V_le_Q_of_data hnm'V
    rw [h.Q_comm _ hBQ _ hXQ]
    exact mul_inv_cancel_right _ _
  have hABV : ⁅m, ρ * m * ρ⁻¹⁆ * ⁅ρ * m * ρ⁻¹, ρ⁻¹ * m * ρ⁆⁻¹ ∈ V := by
    rw [comm_rho_identity' (G := H) ρ m]
    rw [hB_comm]
    exact V.mul_mem hcBV hnm'V
  have hA_Mc : ⁅m, ρ * m * ρ⁻¹⁆ ∈ Mc :=
    h.Q_le_Mc hMh hMc (h.Mh_comm_mem_Q hMh hmMh hm'Mh)
  have hBAV : ρ * ⁅m, ρ * m * ρ⁻¹⁆ * ρ⁻¹ * ⁅m, ρ * m * ρ⁻¹⁆⁻¹ ∈ V := by
    rw [conj_comm_rho_identity ρ m heq]
    rw [zj_mul_inv]
    exact V.inv_mem hABV
  exact h.Mc_fpf_V hMh hMc hA_Mc hBAV

theorem Mc_comm_mem_V {a b : H} (ha : a ∈ Mc) (hb : b ∈ Mc) : a * b * a⁻¹ * b⁻¹ ∈ V := by
  by_cases haQ : a ∈ Q
  · have h1 : b * a * b⁻¹ * a⁻¹ ∈ V := h.Mh_comm_Q hMh (h.Mc_le_Mh hMh hMc hb) haQ
    have h2 : a * b * a⁻¹ * b⁻¹ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by group
    rw [h2]
    exact V.inv_mem h1
  · have hG₀ : ∀ m ∈ Mc, ∀ v ∈ V, m * v * m⁻¹ = v :=
      fun m hm v hv => h.Mh_cent_V hMh (h.Mc_le_Mh hMh hMc hm) hv
    obtain ⟨D, hDmem, _⟩ := h.exists_comm_subgroup hG₀ a
    have hQMc : Q ≤ Mc := h.Q_le_Mc hMh hMc
    have haD : a ∈ D := by
      rw [hDmem a]
      exact ⟨ha, by rw [show a * a * a⁻¹ * a⁻¹ = 1 by group]; exact V.one_mem⟩
    have hρaD : ρ * a * ρ⁻¹ ∈ D := by
      rw [hDmem]
      refine ⟨h.Mc_conj_rho hMh hMc ha, ?_⟩
      have h1 : a * (ρ * a * ρ⁻¹) * a⁻¹ * (ρ * a * ρ⁻¹)⁻¹ ∈ V :=
        h.Mc_comm_rho_mem_V hMh hMc ha
      have h2 : (ρ * a * ρ⁻¹) * a * (ρ * a * ρ⁻¹)⁻¹ * a⁻¹
          = (a * (ρ * a * ρ⁻¹) * a⁻¹ * (ρ * a * ρ⁻¹)⁻¹)⁻¹ := by group
      rw [h2]
      exact V.inv_mem h1
    have hQD : Q ≤ D := by
      intro q hq
      rw [hDmem q]
      refine ⟨hQMc hq, ?_⟩
      have h1 : a * q * a⁻¹ * q⁻¹ ∈ V := h.Mh_comm_Q hMh (h.Mc_le_Mh hMh hMc ha) hq
      have h2 : q * a * q⁻¹ * a⁻¹ = (a * q * a⁻¹ * q⁻¹)⁻¹ := by group
      rw [h2]
      exact V.inv_mem h1
    have hclosure : closure ({a, ρ * a * ρ⁻¹} : Set H) ⊔ Q ≤ D := by
      refine sup_le ?_ hQD
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact haD
      · exact hρaD
    have hMcD : Mc ≤ D := (h.Mc_le_closure hMh hMc ha haQ).trans hclosure
    have hbD : b ∈ D := hMcD hb
    have h1 : b * a * b⁻¹ * a⁻¹ ∈ V := ((hDmem b).mp hbD).2
    have h2 : a * b * a⁻¹ * b⁻¹ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by group
    rw [h2]
    exact V.inv_mem h1

theorem Mc_mul_sq {a b : H} (ha : a ∈ Mc) (hb : b ∈ Mc) :
    a * b * (a * b) = (b * a * b⁻¹ * a⁻¹) * (a * a) * (b * b) := by
  set c : H := b * a * b⁻¹ * a⁻¹ with hcdef
  have hcV : c ∈ V := by rw [hcdef]; exact h.Mc_comm_mem_V hMh hMc hb ha
  have hcent : a * c * a⁻¹ = c := h.Mh_cent_V hMh (h.Mc_le_Mh hMh hMc ha) hcV
  have hca : a * c = c * a := by
    calc a * c = (a * c * a⁻¹) * a := by group
      _ = c * a := by rw [hcent]
  have hba : b * a = c * a * b := by rw [hcdef]; group
  calc a * b * (a * b)
      = a * (b * a) * b := by group
    _ = a * (c * a * b) * b := by rw [hba]
    _ = (a * c) * a * b * b := by group
    _ = (c * a) * a * b * b := by rw [hca]
    _ = c * (a * a) * (b * b) := by group

theorem Mc_sq_central {m x : H} (hm : m ∈ Mc) (hx : x ∈ Mc) : m * m * x = x * (m * m) := by
  set c : H := m * x * m⁻¹ * x⁻¹ with hcdef
  have hcV : c ∈ V := by rw [hcdef]; exact h.Mc_comm_mem_V hMh hMc hm hx
  have hcY : c ∈ Y := h.V_le_Y_of_data hcV
  have hcc : c * c = 1 := h.Y_sq c hcY
  have hcent : m * c * m⁻¹ = c := h.Mh_cent_V hMh (h.Mc_le_Mh hMh hMc hm) hcV
  have hmc : m * c = c * m := by
    calc m * c = (m * c * m⁻¹) * m := by group
      _ = c * m := by rw [hcent]
  have hmx : m * x = c * x * m := by rw [hcdef]; group
  calc m * m * x
      = m * (m * x) := by group
    _ = m * (c * x * m) := by rw [hmx]
    _ = (m * c) * x * m := by group
    _ = (c * m) * x * m := by rw [hmc]
    _ = c * (m * x) * m := by group
    _ = c * (c * x * m) * m := by rw [hmx]
    _ = c * c * x * (m * m) := by group
    _ = x * (m * m) := by rw [hcc]; group

theorem exists_sq_subgroup {K : Subgroup H} (hVK : V ≤ K) :
    ∃ D : Subgroup H, ∀ m, m ∈ D ↔ m ∈ Mc ∧ m * m ∈ K := by
  refine ⟨{ carrier := {m | m ∈ Mc ∧ m * m ∈ K}
            one_mem' := ⟨Mc.one_mem, by simpa using K.one_mem⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun m => Iff.rfl⟩
  · rintro a b ⟨haMc, haK⟩ ⟨hbMc, hbK⟩
    refine ⟨Mc.mul_mem haMc hbMc, ?_⟩
    rw [h.Mc_mul_sq hMh hMc haMc hbMc]
    exact K.mul_mem (K.mul_mem (hVK (h.Mc_comm_mem_V hMh hMc hbMc haMc)) haK) hbK
  · rintro a ⟨haMc, haK⟩
    refine ⟨Mc.inv_mem haMc, ?_⟩
    rw [show a⁻¹ * a⁻¹ = (a * a)⁻¹ by group]
    exact K.inv_mem haK

theorem Mc_sq_dichotomy :
    (∀ m ∈ Mc, m * m ∈ V) ∨ (∀ m ∈ Mc, m ∉ Q → m * m ∉ Y) := by
  by_cases hex : ∃ m₁ ∈ Mc, m₁ ∉ Q ∧ m₁ * m₁ ∈ V
  · left
    obtain ⟨m₁, hm₁Mc, hm₁Q, hm₁V⟩ := hex
    obtain ⟨D, hDmem⟩ := h.exists_sq_subgroup hMh hMc (le_refl V)
    have hQMc : Q ≤ Mc := h.Q_le_Mc hMh hMc
    have hQD : Q ≤ D := by
      intro q hq
      rw [hDmem q]
      exact ⟨hQMc hq, by simpa [pow_two] using h.sq_mem_V q hq⟩
    have hm₁D : m₁ ∈ D := (hDmem m₁).mpr ⟨hm₁Mc, hm₁V⟩
    have hm₁'D : ρ * m₁ * ρ⁻¹ ∈ D := by
      rw [hDmem]
      refine ⟨h.Mc_conj_rho hMh hMc hm₁Mc, ?_⟩
      have hsq : (ρ * m₁ * ρ⁻¹) * (ρ * m₁ * ρ⁻¹) = ρ * (m₁ * m₁) * ρ⁻¹ := by group
      rw [hsq]
      exact h.rho_norm_V (m₁ * m₁) hm₁V
    have hclosure : closure ({m₁, ρ * m₁ * ρ⁻¹} : Set H) ⊔ Q ≤ D := by
      refine sup_le ?_ hQD
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hm₁D
      · exact hm₁'D
    have hMcD : Mc ≤ D := (h.Mc_le_closure hMh hMc hm₁Mc hm₁Q).trans hclosure
    intro m hm
    exact ((hDmem m).mp (hMcD hm)).2
  · right
    intro m hm hmQ hmY
    apply hex
    refine ⟨m, hm, hmQ, ?_⟩
    have hmC : m ∉ centralizer (Y : Set H) := by
      intro hc
      exact hmQ (h.mem_Q_of_mem_Mc_cent_Y hMh hMc hm hc)
    have hfix : m * (m * m) * m⁻¹ = m * m := by group
    exact h.Mh_cent_Y hMh (h.Mc_le_Mh hMh hMc hm) hmC hmY hfix

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
