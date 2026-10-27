module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56SevenAll
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Q

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


@[expose] noncomputable def s56Cm (d : Data G) (q : G) : G := d.pv 7 * q * (d.pv 7)⁻¹ * q⁻¹

theorem Hyp.s56_cm_mem_Q2 (h49 : d.Thm49Statement) (hd : d.Hyp) {q : G} (hq : q ∈ d.s56Q2) :
    d.s56Cm q ∈ d.s56Q2 :=
  hd.s56_Q0_comm_mem_Q2 h49 (hd.s56_pv7_mem_Q0 h49) (hd.s56_Q2_le_Q0 h49 hq)

theorem Hyp.s56_eps_cm (h49 : d.Thm49Statement) (hd : d.Hyp) {q : G} (hq : q ∈ d.s56Q2) :
    d.s56Eps (d.s56Cm q) = d.pv 7 * d.s56Eps q * (d.pv 7)⁻¹ * (d.s56Eps q)⁻¹ := by
  obtain ⟨hct, -⟩ := hd.s56_comm_t h49 (hd.s56_pv7_mem_Q0 h49) hd.s56_pv7_comm_t
    (hd.s56_Q2_le_Q0 h49 hq)
  have h1 := hd.s56_conj_t (d.s56Cm q)
  have h2 : d.s56Cm q * d.t * (d.s56Cm q)⁻¹ = d.t * (d.pv 7 * d.s56Eps q * (d.pv 7)⁻¹ *
      (d.s56Eps q)⁻¹) := hct
  rw [h1] at h2
  exact mul_left_cancel h2

theorem Hyp.s56_exists_q1 (h49 : d.Thm49Statement) (hd : d.Hyp) :
    ∃ q₁ ∈ d.s56Q2, d.s56Eps q₁ = d.pv 8 := by
  obtain ⟨-, -, htrans, -⟩ := hd.s56_structure_M h49
  obtain ⟨m, hm, hmt⟩ := htrans _ (s56_pv8_mem_E d)
  refine ⟨m, hm, ?_⟩
  rw [s56Eps, hmt, ← mul_assoc, hd.t_mul_self, one_mul]

theorem Hyp.s56_cm_mem_E (h49 : d.Thm49Statement) (hd : d.Hyp) {q : G} (hq : q ∈ d.s56Q2)
    (hqN : q ∈ d.N) : d.s56Cm q ∈ d.E := by
  have hq0 := hd.s56_Q2_le_Q0 h49 hq
  have hε := (hd.s56_mem_N_iff_eps h49 hq0).1 hqN
  have hC := (hd.s56_comm_pv7_mem_C_iff h49 hq0).2 hε
  have hcm : d.s56Cm q = (q * d.pv 7 * q⁻¹ * (d.pv 7)⁻¹)⁻¹ := by unfold s56Cm; group
  have hCm : d.s56Cm q ∈ centralizer (d.A : Set G) := by
    rw [hcm]; exact inv_mem hC
  have hF : d.s56Cm q ∈ d.F := by
    have h1 : q * (d.pv 7)⁻¹ * q⁻¹ ∈ d.F := by
      have := hd.s56_N_conj_F h49 hqN (inv_mem hd.s56_pv7_mem_F)
      simpa [mul_assoc] using this
    have e : d.s56Cm q = d.pv 7 * (q * (d.pv 7)⁻¹ * q⁻¹) := by unfold s56Cm; group
    rw [e]
    exact mul_mem hd.s56_pv7_mem_F h1
  exact hd.s56_C_inf_L hCm (s56_F_le_L d hF)

theorem Hyp.s56_exists_z1 (h49 : d.Thm49Statement) (hd : d.Hyp) :
    ∃ z₁ : G, z₁ ∈ d.s56Q2 ∧ z₁ ∈ d.s56Q ∧ d.s56Eps z₁ = d.z ∧
      d.pv 7 * z₁ * (d.pv 7)⁻¹ = z₁⁻¹ ∧
      ∀ q ∈ d.s56Q2, d.s56Cm q ∈ d.E ∨ ∃ e ∈ d.E, d.s56Cm q = z₁ * e := by
  obtain ⟨q₁, hq₁, hε₁⟩ := hd.s56_exists_q1 h49
  have hq₁M : q₁ ∈ d.M := ((s56_mem_Q2_iff).1 hq₁).1
  have hv8 := s56_pv8_mem_E d
  refine ⟨d.s56Cm q₁, hd.s56_cm_mem_Q2 h49 hq₁, ?_, ?_, ?_, ?_⟩
  ·
    have hvQ : d.pv 7 ∈ d.s56Q := hd.s56_J_le_Q h49 (s56_pv7_mem_J d)
    have hN := hd.s56_M_le_normalizer_Q h49 hq₁M
    have hinv : (d.pv 7)⁻¹ ∈ d.s56Q := inv_mem hvQ
    have h1 : q₁ * (d.pv 7)⁻¹ * q₁⁻¹ ∈ d.s56Q := (mem_normalizer_iff.1 hN _).1 hinv
    have e : d.s56Cm q₁ = d.pv 7 * (q₁ * (d.pv 7)⁻¹ * q₁⁻¹) := by unfold s56Cm; group
    rw [e]
    exact mul_mem hvQ h1
  ·
    rw [hd.s56_eps_cm h49 hq₁, hε₁, s56_pv7_conj_pv8 d]
    have hzc : d.pv 8 * d.z = d.z * d.pv 8 := hd.s56_E_comm hv8 hd.s56_z_mem_E
    calc d.pv 8 * d.z * (d.pv 8)⁻¹ = d.z * d.pv 8 * (d.pv 8)⁻¹ := by rw [hzc]
      _ = d.z := by group
  ·
    have hv7 := s56_pv7_inv d
    have hvv := s56_pv7_mul_self d
    unfold s56Cm
    calc d.pv 7 * (d.pv 7 * q₁ * (d.pv 7)⁻¹ * q₁⁻¹) * (d.pv 7)⁻¹
        = (d.pv 7 * d.pv 7) * q₁ * (d.pv 7)⁻¹ * q₁⁻¹ * (d.pv 7)⁻¹ := by group
      _ = q₁ * (d.pv 7)⁻¹ * q₁⁻¹ * (d.pv 7)⁻¹ := by rw [hvv, one_mul]
      _ = q₁ * d.pv 7 * q₁⁻¹ * (d.pv 7)⁻¹ := by rw [hv7]
      _ = (d.pv 7 * q₁ * (d.pv 7)⁻¹ * q₁⁻¹)⁻¹ := by group
  · intro q hq
    by_cases hqN : q ∈ d.N
    · exact Or.inl (hd.s56_cm_mem_E h49 hq hqN)
    · right
      have hq0 := hd.s56_Q2_le_Q0 h49 hq
      have hqε : d.s56Eps q ∉ d.F := fun h => hqN ((hd.s56_mem_N_iff_eps h49 hq0).2 h)
      have hqM : q ∈ d.M := ((s56_mem_Q2_iff).1 hq).1
      have hεE := hd.s56_eps_mem_E hqM
      have hn : q₁⁻¹ * q ∈ d.s56Q2 := mul_mem (inv_mem hq₁) hq
      have hnε : d.s56Eps (q₁⁻¹ * q) ∈ d.F := by
        rw [hd.s56_eps_mul_Q2' (inv_mem hq₁) hq, hd.s56_eps_inv_Q2 hq₁, hε₁]
        rcases hd.s56_E_cases hεE with h | h
        · exact absurd h hqε
        · exact h
      have hnN : q₁⁻¹ * q ∈ d.N :=
        (hd.s56_mem_N_iff_eps h49 (hd.s56_Q2_le_Q0 h49 hn)).2 hnε
      have hcn := hd.s56_cm_mem_E h49 hn hnN
      have hcomm : q₁ * d.s56Cm (q₁⁻¹ * q) * q₁⁻¹ = d.s56Cm (q₁⁻¹ * q) := by
        have := ((s56_mem_Q2_iff).1 hq₁).2 _ hcn
        calc q₁ * d.s56Cm (q₁⁻¹ * q) * q₁⁻¹ = d.s56Cm (q₁⁻¹ * q) * q₁ * q₁⁻¹ := by
              rw [← this]
          _ = d.s56Cm (q₁⁻¹ * q) := by group
      refine ⟨d.s56Cm (q₁⁻¹ * q), hcn, ?_⟩
      have e : d.s56Cm q = d.s56Cm q₁ * (q₁ * d.s56Cm (q₁⁻¹ * q) * q₁⁻¹) := by
        unfold s56Cm; group
      rw [e, hcomm]

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
