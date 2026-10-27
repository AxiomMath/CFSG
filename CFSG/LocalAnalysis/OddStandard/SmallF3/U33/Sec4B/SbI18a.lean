module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18t

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem l18_exists_comm_tau_not_mem_V (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    ∃ m ∈ ctxXi t tau x₁ x₂ rho, m * tau * m⁻¹ * tau⁻¹ ∉ fourGrp x₁ x₂ := by
  obtain ⟨m, hmXi, hmQ⟩ : ∃ m ∈ ctxXi t tau x₁ x₂ rho, m ∉ ctxQ t tau x₁ x₂ rho := by
    by_contra h
    have hle : ctxXi t tau x₁ x₂ rho ≤ ctxQ t tau x₁ x₂ rho := by
      intro m hm
      by_contra hmQ
      exact h ⟨m, hm, hmQ⟩
    have hcard := Subgroup.card_le_of_le hle
    rw [l18_card_Xi hc, IsZ4Z4E4.card hc.q_iso] at hcard
    norm_num at hcard
  have hcQ : m * t * m⁻¹ * t⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    l18_comm_Xi_R_mem_Q hc hmXi (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have hyXi : m * om * m⁻¹ * om⁻¹ ∈ ctxYq t tau x₁ x₂ rho := l18_comm_om_mem_Y hc hmXi
  set c : G := m * t * m⁻¹ * t⁻¹ with hcdef
  set y₁ : G := m * om * m⁻¹ * om⁻¹ with hydef
  set v : G := t * y₁ * t⁻¹ * y₁⁻¹ with hvdef
  set w : G := t * c * t⁻¹ * c⁻¹ with hwdef
  set e : G := om * c * om⁻¹ * c⁻¹ with hedef
  have hcYnot : c ∉ ctxYq t tau x₁ x₂ rho := by
    intro hcY
    rw [hcdef] at hcY
    have hD : t * m * t⁻¹ * m⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
      have hinv := (ctxYq t tau x₁ x₂ rho).inv_mem hcY
      rwa [show (m * t * m⁻¹ * t⁻¹)⁻¹ = t * m * t⁻¹ * m⁻¹ from by group] at hinv
    exact hmQ (l18_Dt_le_Q hc hmXi hD)
  have ht2 : t * t = 1 := by
    have h := (ctx13_relations hc.toCtx13).1
    simpa [pow_two] using h
  have htau_eq : tau = t * (om * t * om⁻¹) := by
    rw [hc.t_om, ← mul_assoc, ht2, one_mul]
  have hmul_t : m * t * m⁻¹ = c * t := by rw [hcdef]; group
  have hmul_om : m * om * m⁻¹ = y₁ * om := by rw [hydef]; group
  have hstep1 : m * tau * m⁻¹ = c * t * y₁ * (om * c * om⁻¹) * t * tau * y₁⁻¹ := by
    conv_lhs => rw [htau_eq]
    have hconj : m * (om * t * om⁻¹) * m⁻¹ = (y₁ * om) * (c * t) * (y₁ * om)⁻¹ := by
      rw [show m * (om * t * om⁻¹) * m⁻¹
            = (m * om * m⁻¹) * (m * t * m⁻¹) * (m * om * m⁻¹)⁻¹ from by group,
          hmul_t, hmul_om]
    rw [show m * (t * (om * t * om⁻¹)) * m⁻¹
          = (m * t * m⁻¹) * (m * (om * t * om⁻¹) * m⁻¹) from by group,
        hmul_t, hconj]
    rw [show (y₁ * om) * (c * t) * (y₁ * om)⁻¹
          = y₁ * om * c * t * om⁻¹ * y₁⁻¹ from by group]
    rw [show y₁ * om * c * t * om⁻¹ * y₁⁻¹
          = y₁ * (om * c * om⁻¹) * (om * t * om⁻¹) * y₁⁻¹ from by group]
    rw [hc.t_om]
    group
  have hconj_y : tau * y₁⁻¹ * tau⁻¹ = y₁⁻¹ := by
    have h : tau * y₁ * tau⁻¹ = y₁ := by
      rw [hc.tau_cent_Y y₁ hyXi]
      group
    rw [show tau * y₁⁻¹ * tau⁻¹ = (tau * y₁ * tau⁻¹)⁻¹ from by group, h]
  have hstep2 : m * tau * m⁻¹ * tau⁻¹
      = c * t * y₁ * (om * c * om⁻¹) * t * y₁⁻¹ := by
    rw [hstep1]
    rw [show c * t * y₁ * (om * c * om⁻¹) * t * tau * y₁⁻¹ * tau⁻¹
          = c * t * y₁ * (om * c * om⁻¹) * t * (tau * y₁⁻¹ * tau⁻¹) from by group,
        hconj_y]
  have hstep3 : c * t * y₁ * (om * c * om⁻¹) * t * y₁⁻¹
      = c * (t * y₁ * t⁻¹) * (t * (om * c * om⁻¹) * t⁻¹) * y₁⁻¹ := by
    calc c * t * y₁ * (om * c * om⁻¹) * t * y₁⁻¹
        = c * (t * y₁ * t⁻¹) * (t * (om * c * om⁻¹) * t⁻¹) * (t * t) * y₁⁻¹ := by
          group
      _ = c * (t * y₁ * t⁻¹) * (t * (om * c * om⁻¹) * t⁻¹) * y₁⁻¹ := by
          rw [ht2]; group
  have h1 : m * tau * m⁻¹ * tau⁻¹
      = c * (t * y₁ * t⁻¹) * (t * (om * c * om⁻¹) * t⁻¹) * y₁⁻¹ :=
    hstep2.trans hstep3
  have hy1Q : y₁ ∈ ctxQ t tau x₁ x₂ rho := by
    rw [hydef]; exact ctxYq_le_ctxQ hyXi
  have hvV : v ∈ fourGrp x₁ x₂ := by
    rw [hvdef]; exact l18_comm_t_Q_mem_V hc.toCtx13 hy1Q
  have hvQ : v ∈ ctxQ t tau x₁ x₂ rho := (l17_V_le_Y hc.toCtx13).trans ctxYq_le_ctxQ hvV
  have hwV : w ∈ fourGrp x₁ x₂ := by
    rw [hwdef]; exact l18_comm_t_Q_mem_V hc.toCtx13 hcQ
  have hwQ : w ∈ ctxQ t tau x₁ x₂ rho := (l17_V_le_Y hc.toCtx13).trans ctxYq_le_ctxQ hwV
  have heY : e ∈ ctxYq t tau x₁ x₂ rho := by
    rw [hedef]; exact Ctx13.comm_om_mem_Y hc.toCtx13 hcQ
  have hteY : t * e * t⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
    l17_K_normalizes_Y hc.toCtx13 t (l17_mem_K hc.toCtx13).1 e heY
  have hteQ : t * e * t⁻¹ ∈ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ hteY
  have hy1invQ : y₁⁻¹ ∈ ctxQ t tau x₁ x₂ rho := (ctxQ t tau x₁ x₂ rho).inv_mem hy1Q
  haveI : IsMulCommutative (ctxQ t tau x₁ x₂ rho) :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (IsZ4Z4E4.comm hc.q_iso a.2 b.2))
  have hA : t * y₁ * t⁻¹ = v * y₁ := by rw [hvdef]; group
  have hD : t * (om * c * om⁻¹) * t⁻¹ = (t * e * t⁻¹) * (w * c) := by
    rw [hedef, hwdef]; group
  have h2' : c * (v * y₁) * ((t * e * t⁻¹) * (w * c))
      = c * c * v * w * (t * e * t⁻¹) * y₁ := by
    have hsub : (⟨c, hcQ⟩ : ctxQ t tau x₁ x₂ rho) *
          ((⟨v, hvQ⟩ : ctxQ t tau x₁ x₂ rho) * (⟨y₁, hy1Q⟩ : ctxQ t tau x₁ x₂ rho)) *
          ((⟨t * e * t⁻¹, hteQ⟩ : ctxQ t tau x₁ x₂ rho) *
            ((⟨w, hwQ⟩ : ctxQ t tau x₁ x₂ rho) * (⟨c, hcQ⟩ : ctxQ t tau x₁ x₂ rho)))
        = (⟨c, hcQ⟩ : ctxQ t tau x₁ x₂ rho) * (⟨c, hcQ⟩ : ctxQ t tau x₁ x₂ rho) *
          (⟨v, hvQ⟩ : ctxQ t tau x₁ x₂ rho) * (⟨w, hwQ⟩ : ctxQ t tau x₁ x₂ rho) *
          (⟨t * e * t⁻¹, hteQ⟩ : ctxQ t tau x₁ x₂ rho) *
          (⟨y₁, hy1Q⟩ : ctxQ t tau x₁ x₂ rho) := by
      ac_rfl
    exact congrArg Subtype.val hsub
  have h2 : c * (t * y₁ * t⁻¹) * (t * (om * c * om⁻¹) * t⁻¹) * y₁⁻¹
      = c * c * v * w * (t * e * t⁻¹) := by
    rw [hA, hD, h2']
    group
  have hmain : m * tau * m⁻¹ * tau⁻¹ = c * c * v * w * (t * e * t⁻¹) := h1.trans h2
  refine ⟨m, hmXi, ?_⟩
  intro hV
  have htV : t * e * t⁻¹ ∈ fourGrp x₁ x₂ := by
    have hccV : c * c ∈ fourGrp x₁ x₂ := by
      simpa [pow_two] using l17_Q_sq_mem hc.toCtx13 c hcQ
    have hprodV : c * c * v * w ∈ fourGrp x₁ x₂ :=
      (fourGrp x₁ x₂).mul_mem ((fourGrp x₁ x₂).mul_mem hccV hvV) hwV
    have heq : t * e * t⁻¹ = (c * c * v * w)⁻¹ * (m * tau * m⁻¹ * tau⁻¹) := by
      rw [hmain]; group
    rw [heq]
    exact (fourGrp x₁ x₂).mul_mem ((fourGrp x₁ x₂).inv_mem hprodV) hV
  have heV : e ∈ fourGrp x₁ x₂ := by
    have hcent : t * e * t⁻¹ ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := by
      rw [hc.Y_cent.1]; exact htV
    obtain ⟨_, hcent2⟩ := Subgroup.mem_inf.mp hcent
    have hcomm : t * (t * e * t⁻¹) = (t * e * t⁻¹) * t :=
      (Subgroup.mem_centralizer_iff.mp hcent2) t (by simp)
    have h1e : e = t⁻¹ * (t * e * t⁻¹) * t := by group
    rw [h1e]
    have h2e : t⁻¹ * (t * e * t⁻¹) * t = t * e * t⁻¹ := by
      rw [show t⁻¹ * (t * e * t⁻¹) * t = t⁻¹ * ((t * e * t⁻¹) * t) from by group,
          ← hcomm]
      group
    rw [h2e]
    exact htV
  have he_comm : e ∈ ⁅ctxQ t tau x₁ x₂ rho, zpowers om⁆ := by
    have hmem : c * om * c⁻¹ * om⁻¹ ∈ ⁅ctxQ t tau x₁ x₂ rho, zpowers om⁆ := by
      have h := Subgroup.commutator_mem_commutator (H₁ := ctxQ t tau x₁ x₂ rho)
        (H₂ := zpowers om) hcQ (Subgroup.mem_zpowers om)
      simpa [commutatorElement_def] using h
    rw [hedef]
    have heq : om * c * om⁻¹ * c⁻¹ = (c * om * c⁻¹ * om⁻¹)⁻¹ := by group
    rw [heq]
    exact (⁅ctxQ t tau x₁ x₂ rho, zpowers om⁆).inv_mem hmem
  have he_one : e = 1 := by
    have hbot : e ∈ (⊥ : Subgroup G) := by
      have : e ∈ ⁅ctxQ t tau x₁ x₂ rho, zpowers om⁆ ⊓ fourGrp x₁ x₂ := ⟨he_comm, heV⟩
      rwa [hc.Q_om.2.2.1] at this
    simpa using hbot
  have hcY : c ∈ ctxYq t tau x₁ x₂ rho := by
    have hc_comm : c ∈ centralizer ({om} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have homc : om * c = c * om := by
        have h := he_one
        rw [hedef] at h
        calc om * c = om * c * om⁻¹ * c⁻¹ * (c * om) := by group
          _ = 1 * (c * om) := by rw [h]
          _ = c * om := by group
      exact homc.symm
    have : c ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({om} : Set G) := ⟨hcQ, hc_comm⟩
    rwa [hc.Q_om.2.2.2.1] at this
  exact hcYnot hcY

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
