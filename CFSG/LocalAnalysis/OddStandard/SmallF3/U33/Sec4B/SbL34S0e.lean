module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped Pointwise
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


section Basic

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem s_not_central {s : G} (hs : s = t ∨ s = tau ∨ s = t * tau) :
    ∃ b ∈ ctxQ t tau x₁ x₂ rho, b * s ≠ s * b := by
  have hsf := s_facts hc hs
  by_contra h
  push_neg at h
  have hV : ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ = fourGrp x₁ x₂ := by
    rcases hs with hst | hst | hst
    · rw [hst]; exact comm_t_eq hc
    · rw [hst]; exact comm_tau_eq hc
    · rw [hst]; exact comm_ttau_eq hc
  have hbot : ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_bot]
    rcases mem_zpowers_eq_one_or_eq hsf.1 hg₂ with rfl | rfl
    · rw [commutatorElement_def]
      group
    · rw [commutatorElement_def, h g₁ hg₁]
      group
  have hVle : fourGrp x₁ x₂ ≤ ⊥ := by rw [← hV]; exact hbot
  exact hc.y_ne_one (Subgroup.mem_bot.mp (hVle (subset_closure (by simp))))

theorem coprime_three_orderOf {a : G} (ha : a ∈ ctxO t tau x₁ x₂) : Nat.Coprime 3 (orderOf a) := by
  have hdvd : orderOf a ∣ Nat.card (ctxU t tau x₁ x₂ lam) :=
    Subgroup.orderOf_dvd_natCard (ctxU t tau x₁ x₂ lam) (O_le_U hc ha)
  rw [card_U hc] at hdvd
  exact (by norm_num : Nat.Coprime 3 (2 ^ 9)).coprime_dvd_right hdvd

theorem ZO_rho_inv {a : G}
    (ha : a ∈ ctxO t tau x₁ x₂ ⊓ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G)) :
    rho * a * rho⁻¹ ∈ ctxO t tau x₁ x₂ ⊓ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_inf]
  refine ⟨(O_normal_M t tau x₁ x₂).2 rho hc.rho_mem_M a ha.1, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro b hb
  have hb' : rho⁻¹ * b * rho ∈ ctxO t tau x₁ x₂ := by
    simpa using (O_normal_M t tau x₁ x₂).2 rho⁻¹ (inv_mem hc.rho_mem_M) b hb
  have h1 : (rho⁻¹ * b * rho) * a = a * (rho⁻¹ * b * rho) :=
    Subgroup.mem_centralizer_iff.mp ha.2 (rho⁻¹ * b * rho) hb'
  calc b * (rho * a * rho⁻¹) = rho * (rho⁻¹ * b * rho) * a * rho⁻¹ := by group
    _ = rho * ((rho⁻¹ * b * rho) * a) * rho⁻¹ := by group
    _ = rho * (a * (rho⁻¹ * b * rho)) * rho⁻¹ := by rw [h1]
    _ = (rho * a * rho⁻¹) * b := by group

theorem T_central_eq_one {n : G} (hn : n ∈ closure ({t, tau} : Set G))
    (hz : n ∈ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G)) : n = 1 := by
  rcases (mem_T_iff hc).mp hn with rfl | rfl | rfl | rfl
  · rfl
  · obtain ⟨b, hbQ, hbne⟩ := s_not_central hc (Or.inl rfl)
    exact absurd (Subgroup.mem_centralizer_iff.mp hz b (hc.Q_le_O hbQ)) hbne
  · obtain ⟨b, hbQ, hbne⟩ := s_not_central hc (Or.inr (Or.inl rfl))
    exact absurd (Subgroup.mem_centralizer_iff.mp hz b (hc.Q_le_O hbQ)) hbne
  · obtain ⟨b, hbQ, hbne⟩ := s_not_central hc (Or.inr (Or.inr rfl))
    exact absurd (Subgroup.mem_centralizer_iff.mp hz b (hc.Q_le_O hbQ)) hbne

theorem ZO_cube_mem_Q {a : G}
    (ha : a ∈ ctxO t tau x₁ x₂ ⊓ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G)) :
    a * a * a ∈ ctxQ t tau x₁ x₂ rho := by
  have h3 : rho * rho * rho = 1 := by
    have h := pow_orderOf_eq_one rho
    rw [hc.ord_rho] at h
    rw [← pow_two, ← pow_succ]
    exact h
  have hcomm : ∀ {u v : G},
      u ∈ ctxO t tau x₁ x₂ ⊓ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) →
      v ∈ ctxO t tau x₁ x₂ ⊓ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) →
      u * v = v * u := by
    intro u v hu hv
    exact (Subgroup.mem_centralizer_iff.mp hu.2 v hv.1).symm
  set b : G := rho * a * rho⁻¹ with hb_def
  set c : G := rho * b * rho⁻¹ with hc_def
  have hb : b ∈ ctxO t tau x₁ x₂ ⊓ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
    rw [hb_def]; exact ZO_rho_inv hc ha
  have hcZ : c ∈ ctxO t tau x₁ x₂ ⊓ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
    rw [hc_def]; exact ZO_rho_inv hc hb
  have hρa : rho * a * rho⁻¹ = b := hb_def.symm
  have hρb : rho * b * rho⁻¹ = c := hc_def.symm
  have hρc : rho * c * rho⁻¹ = a := by
    rw [hc_def, hb_def]
    calc rho * (rho * (rho * a * rho⁻¹) * rho⁻¹) * rho⁻¹
        = (rho * rho * rho) * a * (rho * rho * rho)⁻¹ := by group
      _ = a := by rw [h3]; group
  have hbc : b * c = c * b := hcomm hb hcZ
  have hba : b * a = a * b := hcomm hb ha
  have hca : c * a = a * c := hcomm hcZ ha
  have hbca : b * c * a = a * b * c := by
    calc b * c * a = c * b * a := by rw [hbc]
      _ = c * (b * a) := by group
      _ = c * (a * b) := by rw [hba]
      _ = c * a * b := by group
      _ = a * c * b := by rw [hca]
      _ = a * (c * b) := by group
      _ = a * (b * c) := by rw [hbc]
      _ = a * b * c := by group
  have hn : a * b * c ∈
      ctxO t tau x₁ x₂ ⊓ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) :=
    mul_mem (mul_mem ha hb) hcZ
  have hfix : rho * (a * b * c) * rho⁻¹ = a * b * c := by
    calc rho * (a * b * c) * rho⁻¹
        = (rho * a * rho⁻¹) * (rho * b * rho⁻¹) * (rho * c * rho⁻¹) := by group
      _ = b * c * a := by rw [hρa, hρb, hρc]
      _ = a * b * c := hbca
  have hnCO : a * b * c ∈ ctxCO t tau x₁ x₂ rho := by
    rw [ctxCO, Subgroup.mem_inf]
    refine ⟨hn.1, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h1 : rho * (a * b * c) = (a * b * c) * rho := by
      calc rho * (a * b * c) = rho * (a * b * c) * rho⁻¹ * rho := by group
        _ = (a * b * c) * rho := by rw [hfix]
    exact h1.symm
  have hnT : a * b * c ∈ closure ({t, tau} : Set G) := by
    rw [hc.CO_rho] at hnCO
    exact hnCO
  have hn1 : a * b * c = 1 := T_central_eq_one hc hnT hn.2
  have hbc1 : b * c = a⁻¹ := by
    have h : a * (b * c) = 1 := by rw [← mul_assoc]; exact hn1
    exact eq_inv_of_mul_eq_one_right h
  have hca_inv : c⁻¹ * a = a * c⁻¹ := by
    calc c⁻¹ * a = c⁻¹ * (a * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * a) * c⁻¹ := by rw [hca]
      _ = a * c⁻¹ := by group
  have hbc_inv : c⁻¹ * b⁻¹ = a := by
    calc c⁻¹ * b⁻¹ = (b * c)⁻¹ := by group
      _ = (a⁻¹)⁻¹ := by rw [hbc1]
      _ = a := by group
  have hcalc : (a * c⁻¹) * (a * b⁻¹) = a * a * a := by
    calc (a * c⁻¹) * (a * b⁻¹) = a * (c⁻¹ * a) * b⁻¹ := by group
      _ = a * (a * c⁻¹) * b⁻¹ := by rw [hca_inv]
      _ = a * a * (c⁻¹ * b⁻¹) := by group
      _ = a * a * a := by rw [hbc_inv]
  have hQ1 : a * b⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    have h : a * rho * a⁻¹ * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      Subgroup.commutator_mem_commutator ha.1 (Subgroup.mem_zpowers rho)
    rwa [show a * b⁻¹ = a * rho * a⁻¹ * rho⁻¹ by rw [hb_def]; group]
  have hQ2 : a * c⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    have h : a * rho ^ 2 * a⁻¹ * (rho ^ 2)⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      Subgroup.commutator_mem_commutator ha.1 (pow_mem (Subgroup.mem_zpowers rho) 2)
    rwa [show a * c⁻¹ = a * rho ^ 2 * a⁻¹ * (rho ^ 2)⁻¹ by rw [hc_def, hb_def]; group]
  rw [← hcalc]
  exact mul_mem hQ2 hQ1

theorem ZO_le_Q {a : G}
    (ha : a ∈ ctxO t tau x₁ x₂ ⊓ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G)) :
    a ∈ ctxQ t tau x₁ x₂ rho := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (coprime_three_orderOf hc ha.1)
  have h3a : a ^ 3 ∈ ctxQ t tau x₁ x₂ rho := by
    rw [show a ^ 3 = a * a * a by
      rw [← pow_two, ← pow_succ]]
    exact ZO_cube_mem_Q hc ha
  rw [← hm]
  exact pow_mem h3a m

theorem O_comm_eq : ⁅ctxO t tau x₁ x₂, ctxO t tau x₁ x₂⁆ = fourGrp x₁ x₂ := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    exact O_comm_le hc ha hb
  · rw [← comm_t_eq hc]
    exact Subgroup.commutator_mono hc.Q_le_O (Subgroup.zpowers_le.mpr hc.t_mem_O)

end Basic

section Main

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau) (hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho))
include hc hs

theorem Z_O_eq : ctxO t tau x₁ x₂ ⊓ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) =
    fourGrp x₁ x₂ := by
  refine le_antisymm ?_ ?_
  · intro a ha
    have haQ : a ∈ ctxQ t tau x₁ x₂ rho := ZO_le_Q hc ha
    have haCQ : a ∈ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun b hb =>
        Subgroup.mem_centralizer_iff.mp ha.2 b (hc.Q_le_O hb)
    have hmem : a ∈ ctxQ t tau x₁ x₂ rho ⊓
        centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := ⟨haQ, haCQ⟩
    rw [Z_Q hc hs] at hmem
    exact hmem
  · intro v hv
    exact ⟨V_le_O hc hv, Subgroup.mem_centralizer_iff.mpr fun b hb => V_comm_O hc hb hv⟩

end Main

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
