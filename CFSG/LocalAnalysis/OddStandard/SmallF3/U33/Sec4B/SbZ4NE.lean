module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4FB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z

variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
include hz

theorem comm_Y_t_swap {a : G} (ha : a ∈ ctxYq t tau x₁ x₂ rho) :
    a * t * a⁻¹ * t⁻¹ = t * a * t⁻¹ * a⁻¹ := by
  have ha' : t * a * t⁻¹ ∈ ctxYq t tau x₁ x₂ rho := hz.normal_Y.2 t hz.t_mem_M a ha
  have ha'a : a * (t * a * t⁻¹) = (t * a * t⁻¹) * a :=
    hz.nPre.Y_comm a ha (t * a * t⁻¹) ha'
  have hasq : a * a = 1 := by simpa [pow_two] using hz.nPre.Y_sq ha
  have ha'sq : (t * a * t⁻¹) * (t * a * t⁻¹) = 1 := by
    simpa [pow_two] using hz.nPre.Y_sq ha'
  calc a * t * a⁻¹ * t⁻¹ = a * (t * a * t⁻¹)⁻¹ := by group
    _ = a * (t * a * t⁻¹) := by rw [inv_eq_of_mul_eq_one_right ha'sq]
    _ = (t * a * t⁻¹) * a := ha'a
    _ = (t * a * t⁻¹) * a⁻¹ := by rw [inv_eq_of_mul_eq_one_right hasq]
    _ = t * a * t⁻¹ * a⁻¹ := by group

theorem exists_decomp_of_comm_sq {w : G} (hw : w ∈ ctxWN t tau x₁ x₂ rho)
    (h : (w * t * w⁻¹ * t⁻¹) ^ 2 = 1) :
    ∃ b ∈ baseGrp x₁ x₂, ∃ a ∈ ctxYq t tau x₁ x₂ rho, w = b * a := by
  have hcQm : w * t * w⁻¹ * t⁻¹ ∈ ctxQm t tau x₁ x₂ rho := hz.comm_W_t_mem_Qm hw
  obtain ⟨hcQ, hcCent⟩ := hcQm
  have hcinv : t * (w * t * w⁻¹ * t⁻¹) * t⁻¹ = (w * t * w⁻¹ * t⁻¹)⁻¹ :=
    (hz.nGood.mem_cent_ttau_iff hz.tau_inv_Q hcQ).mp hcCent
  have hcY : w * t * w⁻¹ * t⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
    (hz.mem_Y_iff _).mpr ⟨hcQ, h⟩
  have hcsq : (w * t * w⁻¹ * t⁻¹) * (w * t * w⁻¹ * t⁻¹) = 1 := by
    simpa [pow_two] using h
  have hcinvc : (w * t * w⁻¹ * t⁻¹)⁻¹ = w * t * w⁻¹ * t⁻¹ :=
    inv_eq_of_mul_eq_one_right hcsq
  have hct : t * (w * t * w⁻¹ * t⁻¹) = (w * t * w⁻¹ * t⁻¹) * t := by
    calc t * (w * t * w⁻¹ * t⁻¹)
        = (t * (w * t * w⁻¹ * t⁻¹) * t⁻¹) * t := by group
      _ = (w * t * w⁻¹ * t⁻¹) * t := by rw [hcinv, hcinvc]
  have hcV : w * t * w⁻¹ * t⁻¹ ∈ fourGrp x₁ x₂ := by
    have : w * t * w⁻¹ * t⁻¹ ∈
        ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
      ⟨hcY, mem_centralizer_singleton_iff.mpr hct.symm⟩
    rwa [hz.CY_t] at this
  obtain ⟨a, haY, hacomm⟩ := hz.comm_Y_t_surj _ hcV
  have haW : a ∈ ctxWN t tau x₁ x₂ rho := hz.Y_le_ctxWN haY
  have hbW : w * a⁻¹ ∈ ctxWN t tau x₁ x₂ rho := mul_mem hw (inv_mem haW)
  refine ⟨w * a⁻¹, ?_, a, haY, by group⟩
  have hmul := hz.comm_W_t_mul hbW haW
  have hcomm_a : a * t * a⁻¹ * t⁻¹ = w * t * w⁻¹ * t⁻¹ :=
    (hz.comm_Y_t_swap haY).trans hacomm
  have hkey : w * t * w⁻¹ * t⁻¹ =
      (w * a⁻¹ * t * (w * a⁻¹)⁻¹ * t⁻¹) * (w * t * w⁻¹ * t⁻¹) := by
    have h1 := hmul
    rw [show (w * a⁻¹) * a = w from by group, hcomm_a] at h1
    exact h1
  have hd1 : w * a⁻¹ * t * (w * a⁻¹)⁻¹ * t⁻¹ = 1 := by
    calc w * a⁻¹ * t * (w * a⁻¹)⁻¹ * t⁻¹
        = ((w * a⁻¹ * t * (w * a⁻¹)⁻¹ * t⁻¹) * (w * t * w⁻¹ * t⁻¹)) *
            (w * t * w⁻¹ * t⁻¹)⁻¹ := by group
      _ = (w * t * w⁻¹ * t⁻¹) * (w * t * w⁻¹ * t⁻¹)⁻¹ := by rw [← hkey]
      _ = 1 := mul_inv_cancel _
  have hbB : w * a⁻¹ ∈ baseGrp x₁ x₂ := by
    have h1 : w * a⁻¹ * t * (w * a⁻¹)⁻¹ = t := by
      have h2 := mul_eq_one_iff_eq_inv.mp hd1
      simpa using h2
    have h2 : (w * a⁻¹) * t = t * (w * a⁻¹) := by
      calc (w * a⁻¹) * t = (w * a⁻¹ * t * (w * a⁻¹)⁻¹) * (w * a⁻¹) := by group
        _ = t * (w * a⁻¹) := by rw [h1]
    have hmem : w * a⁻¹ ∈ ctxWN t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
      ⟨hbW, mem_centralizer_singleton_iff.mpr h2⟩
    rwa [hz.ctxWN_inf_centralizer_t] at hmem
  exact hbB

theorem W_invol_mem_Y {w : G} (hw : w ∈ ctxWN t tau x₁ x₂ rho) (h2 : w ^ 2 = 1) :
    w ∈ ctxYq t tau x₁ x₂ rho := by
  have hww : w * w = 1 := by simpa [pow_two] using h2
  have hmul := hz.comm_W_t_mul hw hw
  rw [hww] at hmul
  have hcomm2 : (w * t * w⁻¹ * t⁻¹) ^ 2 = 1 := by
    rw [pow_two, ← hmul]
    group
  obtain ⟨b, hbB, a, haY, hwba⟩ := hz.exists_decomp_of_comm_sq hw hcomm2
  have hbQ : b ∈ ctxQ t tau x₁ x₂ rho := hz.base_le_Q hbB
  have hba : b * a = a * b := hz.nPre.Q_comm b hbQ a (hz.nPre.Y_le_Q haY)
  have hbsq : b ^ 2 = 1 := by
    have hw2' : (b * a) ^ 2 = 1 := by rw [← hwba]; exact h2
    rwa [Commute.mul_pow ((commute_iff_eq b a).mpr hba), hz.nPre.Y_sq haY,
      mul_one] at hw2'
  have hbY : b ∈ ctxYq t tau x₁ x₂ rho := (hz.mem_Y_iff b).mpr ⟨hbQ, hbsq⟩
  rw [hwba]
  exact mul_mem hbY haY

theorem cent_tau_ctxWN {w : G} (hw : w ∈ ctxWN t tau x₁ x₂ rho)
    (h : tau * w * tau⁻¹ = w) : w ∈ ctxYq t tau x₁ x₂ rho := by
  have htau_t_conj : tau * t * tau⁻¹ = t := by
    rw [hz.t_comm_tau.symm, mul_assoc, mul_inv_cancel, mul_one]
  have htauc : tau * (w * t * w⁻¹ * t⁻¹) * tau⁻¹ = w * t * w⁻¹ * t⁻¹ := by
    calc tau * (w * t * w⁻¹ * t⁻¹) * tau⁻¹
        = (tau * w * tau⁻¹) * (tau * t * tau⁻¹) *
            (tau * w * tau⁻¹)⁻¹ * (tau * t * tau⁻¹)⁻¹ := by group
      _ = w * t * w⁻¹ * t⁻¹ := by rw [h, htau_t_conj]
  have hcQ : w * t * w⁻¹ * t⁻¹ ∈ ctxQ t tau x₁ x₂ rho := (hz.mem_ctxWN_iff.mp hw).2
  have hcinv : tau * (w * t * w⁻¹ * t⁻¹) * tau⁻¹ = (w * t * w⁻¹ * t⁻¹)⁻¹ :=
    hz.tau_inv_Q _ hcQ
  have h1 : w * t * w⁻¹ * t⁻¹ = (w * t * w⁻¹ * t⁻¹)⁻¹ := by
    calc w * t * w⁻¹ * t⁻¹ = tau * (w * t * w⁻¹ * t⁻¹) * tau⁻¹ := htauc.symm
      _ = (w * t * w⁻¹ * t⁻¹)⁻¹ := hcinv
  have hc2 : (w * t * w⁻¹ * t⁻¹) ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr h1
  obtain ⟨b, hbB, a, haY, hwba⟩ := hz.exists_decomp_of_comm_sq hw hc2
  have hbQ : b ∈ ctxQ t tau x₁ x₂ rho := hz.base_le_Q hbB
  have hb_eq : b = w * a⁻¹ := by rw [hwba]; group
  have htau_a : tau * a * tau⁻¹ = a := by
    rw [hz.tau_cent_Y a haY, mul_assoc, mul_inv_cancel, mul_one]
  have htau_b : tau * b * tau⁻¹ = b := by
    rw [hb_eq]
    calc tau * (w * a⁻¹) * tau⁻¹ = (tau * w * tau⁻¹) * (tau * a * tau⁻¹)⁻¹ := by group
      _ = w * a⁻¹ := by rw [h, htau_a]
  have hbinv : tau * b * tau⁻¹ = b⁻¹ := hz.tau_inv_Q b hbQ
  have hbsq : b ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr (htau_b.symm.trans hbinv)
  have hbY : b ∈ ctxYq t tau x₁ x₂ rho := (hz.mem_Y_iff b).mpr ⟨hbQ, hbsq⟩
  rw [hwba]
  exact mul_mem hbY haY

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
