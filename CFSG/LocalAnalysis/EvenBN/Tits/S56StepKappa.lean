module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps
public import CFSG.LocalAnalysis.EvenBN.Tits.S56P517

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped Pointwise commutatorElement

namespace Data

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def S56KappaBit (d : Data G) : Prop :=
  ∃ x ∈ d.s56V ⊓ d.N, d.s56Eps x ∉ d.s56U10 ∧
    x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ ∈ d.s56U11

end Defs

section Props

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Hyp.s56_U10_le_E (hd : d.Hyp) : d.s56U10 ≤ d.E := fun x hx => by
  rcases s56_U10_cases hx with h | ⟨u, hu, rfl⟩
  · exact s56_U11_le_E d hd h
  · exact mul_mem hd.s56_pv10_mem_E (s56_U11_le_E d hd hu)

theorem Hyp.s56_U10_le_E_inf_F (hd : d.Hyp) : d.s56U10 ≤ d.E ⊓ d.F :=
  le_inf hd.s56_U10_le_E (s56_U10_le_F d)

theorem Hyp.s56_mul_mem_U10_of_not_mem (hd : d.Hyp) {e e' : G} (he : e ∈ d.E ⊓ d.F)
    (he' : e' ∈ d.E ⊓ d.F) (hne : e ∉ d.s56U10) (hne' : e' ∉ d.s56U10) : e * e' ∈ d.s56U10 := by
  have hEcomm : ∀ a ∈ d.s56U10, e * a = a * e := fun a ha =>
    hd.s56_E_comm (mem_inf.1 he).1 (hd.s56_U10_le_E ha)
  have hee : e * e = 1 := hd.s56_E_sq (mem_inf.1 he).1
  have hJ : d.s56U10 ⊔ zpowers e = d.E ⊓ d.F := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hd.s56_U10_le_E_inf_F (zpowers_le.2 he)) ?_
    have hdvd := Subgroup.card_dvd_of_le (le_sup_left : d.s56U10 ≤ d.s56U10 ⊔ zpowers e)
    rw [s56_card_U10] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    have hne8 : Nat.card ↥(d.s56U10 ⊔ zpowers e) ≠ 8 := fun h8 => hne (by
      have hle : d.s56U10 ⊔ zpowers e ≤ d.s56U10 :=
        (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h8, s56_card_U10])).ge
      exact hle (mem_sup_right (mem_zpowers e)))
    have hpos : 0 < Nat.card ↥(d.s56U10 ⊔ zpowers e) := Nat.card_pos
    rw [hd.s56_card_E_inf_F, hk]
    rw [hk] at hne8 hpos
    omega
  have he'J : e' ∈ d.s56U10 ⊔ zpowers e := by rw [hJ]; exact he'
  rcases s56y_mem_sup_zpowers hEcomm (by rw [hee]; exact one_mem _) he'J with h | ⟨a, ha, rfl⟩
  · exact absurd h hne'
  · have : e * (e * a) = a := by rw [← mul_assoc, hee, one_mul]
    rw [this]
    exact ha

theorem Hyp.s56_comm_F_of_eps_mem_U10 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) {x : G} (hx : x ∈ d.s56V ⊓ d.N) (hε : d.s56Eps x ∈ d.s56U10) :
    ∀ f ∈ d.F, x * f * x⁻¹ * f⁻¹ ∈ d.s56U11 := by
  obtain ⟨hxV, hxN⟩ := mem_inf.1 hx
  have hxP0 : x ∈ d.s56P0 := hd.s56_Q2_inf_N_le_P0 h49 hxV.2 hxN
  have hxP10 : x ∈ d.s56P10 :=
    (hd.s56_mem_P10_iff h49 hxP0).2 (s56_V_comm_E hxV hd.s56_pv10_mem_E)
  exact hd.s56_P10_comm_F_of_comm_B h49 hz hxP10 (hd.s56_comm_B_le_U10_of_eps h49 hxP0 hε)

theorem Hyp.s56Kappa_of_bit (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hb : d.S56KappaBit) : d.S56Kappa := by
  obtain ⟨x₀, hx₀, hx₀ε, hx₀c⟩ := hb
  obtain ⟨hx₀V, hx₀N⟩ := mem_inf.1 hx₀
  have hx₀F : ∀ f ∈ d.F, x₀ * f * x₀⁻¹ * f⁻¹ ∈ d.s56U11 := by
    intro f hf
    rcases Hyp.s56_F_cases d hf with hfE | hfE
    · have h1 : x₀ * f * x₀⁻¹ * f⁻¹ = 1 := by rw [s56_V_comm_E hx₀V hfE]; group
      rw [h1]
      exact one_mem _
    · have hf' : f = d.pv 7 * (d.pv 7 * f) := by
        rw [← mul_assoc, s56_pv7_mul_self, one_mul]
      have hxe : x₀ * (d.pv 7 * f) * x₀⁻¹ = d.pv 7 * f := by
        rw [s56_V_comm_E hx₀V hfE]; group
      have h1 : x₀ * f * x₀⁻¹ * f⁻¹ = x₀ * d.pv 7 * x₀⁻¹ * (d.pv 7)⁻¹ := by
        generalize d.pv 7 * f = e at hf' hxe
        rw [hf']
        calc x₀ * (d.pv 7 * e) * x₀⁻¹ * (d.pv 7 * e)⁻¹
            = (x₀ * d.pv 7 * x₀⁻¹) * (x₀ * e * x₀⁻¹) * e⁻¹ * (d.pv 7)⁻¹ := by group
          _ = x₀ * d.pv 7 * x₀⁻¹ * (d.pv 7)⁻¹ := by rw [hxe]; group
      rw [h1]
      exact hx₀c
  intro x hx f hf
  by_cases hxε : d.s56Eps x ∈ d.s56U10
  · exact hd.s56_comm_F_of_eps_mem_U10 h49 hz hx hxε f hf
  · obtain ⟨hxV, hxN⟩ := mem_inf.1 hx
    have haV : x * x₀⁻¹ ∈ d.s56V := mul_mem hxV (inv_mem hx₀V)
    have haN : x * x₀⁻¹ ∈ d.N := mul_mem hxN (inv_mem hx₀N)
    have haε : d.s56Eps (x * x₀⁻¹) ∈ d.s56U10 := by
      rw [hd.s56_eps_mul_Q2' hxV.2 (inv_mem hx₀V).2, hd.s56_eps_inv_Q2 hx₀V.2]
      exact hd.s56_mul_mem_U10_of_not_mem
        (mem_inf.2 ⟨hd.s56_V_eps_mem_E hxV, hd.s56_eps_mem_F_of_N h49 hxN⟩)
        (mem_inf.2 ⟨hd.s56_V_eps_mem_E hx₀V, hd.s56_eps_mem_F_of_N h49 hx₀N⟩) hxε hx₀ε
    have h1 := hd.s56_comm_F_of_eps_mem_U10 h49 hz (mem_inf.2 ⟨haV, haN⟩) haε f hf
    have h2 := hx₀F f hf
    have e : x * f * x⁻¹ * f⁻¹ = (x * x₀⁻¹) * (x₀ * f * x₀⁻¹ * f⁻¹) * (x * x₀⁻¹)⁻¹ *
        ((x * x₀⁻¹) * f * (x * x₀⁻¹)⁻¹ * f⁻¹) := by group
    rw [e]
    exact mul_mem (hd.s56_N_conj_U11 h49 haN h2) h1

end Props

end Data

namespace N

section StepKappaBit

@[expose] def StepKappaBit : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G},
    d.Thm49Statement → d.Hyp → d.S56KappaBit

end StepKappaBit

section Proofs

theorem stepKappa_of_bit (sB : StepKappaBit) : StepKappa := by
  intro G _ _ d h49 hd
  obtain ⟨z₀, hz⟩ := hd.s56_exists_S56Z0 h49
  exact hd.s56Kappa_of_bit h49 hz (sB h49 hd)

end Proofs

end N

end CFSG.LocalAnalysis.EvenBN.Tits
