module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16G

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {K Y Q : Subgroup G} {t rho z u fz fu : G}

private lemma c16_fz_not_mem_K (H : C16Ab K Y Q t rho z u fz fu) : fz ∉ K := by
  intro hfz
  have h1 : ⁅fz, t⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (H.K_comm_t fz hfz)
  rw [H.fz_t] at h1
  exact H.kb.z_ne_one h1

private lemma c16_fu_not_mem_K (H : C16Ab K Y Q t rho z u fz fu) : fu ∉ K := by
  intro hfu
  have h1 : ⁅fu, t⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (H.K_comm_t fu hfu)
  rw [H.fu_t] at h1
  exact H.kb.u_ne_one h1

private lemma c16_fzfu_not_mem_K (H : C16Ab K Y Q t rho z u fz fu) : fz * fu ∉ K := by
  intro h
  have h1 : ⁅fz * fu, t⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (H.K_comm_t (fz * fu) h)
  rw [c16_N_mul H H.fz_mem H.fu_mem, H.fz_t, H.fu_t] at h1
  have h2 : z * u = z * z := by rw [h1, H.kb.z_sq]
  exact H.kb.z_ne_u (mul_left_cancel h2).symm

theorem c16_beta_rho (H : C16Ab K Y Q t rho z u fz fu) {q : G} (hq : q ∈ Q) :
    c16Beta z u fz fu (rho * q * rho⁻¹) = c16Theta (c16Beta z u fz fu q) := by
  have haK : ⁅q, fz⁆ ∈ K := H.Q_comm_Y q hq fz H.fz_mem
  have hbK : ⁅q, fu⁆ ∈ K := H.Q_comm_Y q hq fu H.fu_mem
  have habK : ⁅q, fz⁆ * ⁅q, fu⁆ ∈ K := K.mul_mem haK hbK
  have hfu : ⁅rho * q * rho⁻¹, fu⁆ = rho * ⁅q, fz⁆ * rho⁻¹ := by
    rw [H.fu_def, ← conjugate_commutatorElement]
  have hfz : ⁅rho * q * rho⁻¹, fz⁆ = rho * (⁅q, fz⁆ * ⁅q, fu⁆) * rho⁻¹ := by
    obtain ⟨κ, hκK, hκ⟩ := c16_rho_inv_fz H
    have hκY : κ ∈ Y := H.K_le_Y hκK
    have hfuY : fz * fu ∈ Y := Y.mul_mem H.fz_mem H.fu_mem
    have hmid : ⁅q, fz * fu * κ⁆ = ⁅q, fz⁆ * ⁅q, fu⁆ := by
      rw [c16_comm_mul_right H hq hfuY hκY, c16_comm_mul_right H hq H.fz_mem H.fu_mem]
      have hqκ : ⁅q, κ⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (H.Q_cent_K q hq κ hκK)
      rw [hqκ, mul_one]
    have hw : fz = rho * (fz * fu * κ) * rho⁻¹ := by rw [← hκ]; group
    calc ⁅rho * q * rho⁻¹, fz⁆
        = ⁅rho * q * rho⁻¹, rho * (fz * fu * κ) * rho⁻¹⁆ := by
            conv_lhs => rw [hw]
      _ = rho * ⁅q, fz * fu * κ⁆ * rho⁻¹ := by rw [← conjugate_commutatorElement]
      _ = rho * (⁅q, fz⁆ * ⁅q, fu⁆) * rho⁻¹ := by rw [hmid]
  apply Prod.ext
  · show c16cK z u ⁅rho * q * rho⁻¹, fz⁆
      = c16Rho0 (c16cK z u ⁅q, fz⁆ + c16cK z u ⁅q, fu⁆)
    rw [hfz, c16cK_rho H.kb H.rho_z H.rho_u habK, c16cK_mul H.kb haK hbK]
  · show c16cK z u ⁅rho * q * rho⁻¹, fu⁆ = c16Rho0 (c16cK z u ⁅q, fz⁆)
    rw [hfu, c16cK_rho H.kb H.rho_z H.rho_u haK]

theorem c16_beta_pplus (H : C16Ab K Y Q t rho z u fz fu) {q : G} (hq : q ∈ Q) :
    c16Pplus (c16Beta z u fz fu q) ↔ ∃ f ∈ Y, f ∉ K ∧ q * f * q⁻¹ = f := by
  have haK : ⁅q, fz⁆ ∈ K := H.Q_comm_Y q hq fz H.fz_mem
  have hbK : ⁅q, fu⁆ ∈ K := H.Q_comm_Y q hq fu H.fu_mem
  have habK : ⁅q, fz⁆ * ⁅q, fu⁆ ∈ K := K.mul_mem haK hbK
  constructor
  · intro hp
    unfold c16Pplus at hp
    rcases hp with h1 | h2 | h3
    · refine ⟨fz, H.fz_mem, c16_fz_not_mem_K H, ?_⟩
      have h1' : c16cK z u ⁅q, fz⁆ = 0 := by simpa [c16Beta] using h1
      have hcomm : q * fz = fz * q :=
        commutatorElement_eq_one_iff_mul_comm.mp ((c16cK_eq_zero H.kb haK).mp h1')
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    · refine ⟨fu, H.fu_mem, c16_fu_not_mem_K H, ?_⟩
      have h2' : c16cK z u ⁅q, fu⁆ = 0 := by simpa [c16Beta] using h2
      have hcomm : q * fu = fu * q :=
        commutatorElement_eq_one_iff_mul_comm.mp ((c16cK_eq_zero H.kb hbK).mp h2')
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    · refine ⟨fz * fu, Y.mul_mem H.fz_mem H.fu_mem, c16_fzfu_not_mem_K H, ?_⟩
      have h3' : c16cK z u ⁅q, fz⁆ + c16cK z u ⁅q, fu⁆ = 0 := by
        simpa [c16Beta] using h3
      have hzero : c16cK z u (⁅q, fz⁆ * ⁅q, fu⁆) = 0 := by
        rw [c16cK_mul H.kb haK hbK]; exact h3'
      have hone : ⁅q, fz⁆ * ⁅q, fu⁆ = 1 := (c16cK_eq_zero H.kb habK).mp hzero
      have hcomm : q * (fz * fu) = (fz * fu) * q :=
        commutatorElement_eq_one_iff_mul_comm.mp
          (by rw [c16_comm_mul_right H hq H.fz_mem H.fu_mem, hone])
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  · rintro ⟨f, hfY, hfK, hfix⟩
    have hcomm : q * f = f * q := by
      have h := congrArg (fun x => x * q) hfix
      simpa [mul_assoc] using h
    have hcommut : ⁅q, f⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm
    rcases c16_Y_cases H hfY with ⟨κ, hκK, hf' | hf' | hf' | hf'⟩
    · exact absurd (hf' ▸ hκK) hfK
    · unfold c16Pplus; left
      have hκY : κ ∈ Y := H.K_le_Y hκK
      have hκq : ⁅q, κ⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (H.Q_cent_K q hq κ hκK)
      have h1 : ⁅q, fz⁆ = 1 := by
        have h := c16_comm_mul_right H hq hκY H.fz_mem
        rw [← hf', hcommut, hκq, one_mul] at h
        exact h.symm
      show c16cK z u ⁅q, fz⁆ = 0
      rw [h1, c16cK_one]
    · unfold c16Pplus; right; left
      have hκY : κ ∈ Y := H.K_le_Y hκK
      have hκq : ⁅q, κ⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (H.Q_cent_K q hq κ hκK)
      have h2 : ⁅q, fu⁆ = 1 := by
        have h := c16_comm_mul_right H hq hκY H.fu_mem
        rw [← hf', hcommut, hκq, one_mul] at h
        exact h.symm
      show c16cK z u ⁅q, fu⁆ = 0
      rw [h2, c16cK_one]
    · unfold c16Pplus; right; right
      have hκY : κ ∈ Y := H.K_le_Y hκK
      have hκq : ⁅q, κ⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (H.Q_cent_K q hq κ hκK)
      have hfuY : fz * fu ∈ Y := Y.mul_mem H.fz_mem H.fu_mem
      have h1 : ⁅q, fz * fu⁆ = 1 := by
        have h := c16_comm_mul_right H hq hκY hfuY
        rw [← hf', hcommut, hκq, one_mul] at h
        exact h.symm
      have h2 : ⁅q, fz⁆ * ⁅q, fu⁆ = 1 := by
        rw [← c16_comm_mul_right H hq H.fz_mem H.fu_mem]; exact h1
      show c16cK z u ⁅q, fz⁆ + c16cK z u ⁅q, fu⁆ = 0
      rw [← c16cK_mul H.kb haK hbK, h2, c16cK_one]

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
