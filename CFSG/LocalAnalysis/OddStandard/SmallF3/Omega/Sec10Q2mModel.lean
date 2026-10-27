module

public import Certificates.Certificate442019
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelF1051
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TypeDict

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

local notation "z0" => Certificates.OmegaT0.z0 ()

theorem q2m_check_true :
    Certificates.OmegaQ2m.check () = true :=
  Certificates.certificate442019

theorem q2m_parts :
    Certificates.OmegaQ2m.conjChk (elemsT QP45) Pk.tA z0 = true ∧
      Certificates.OmegaQ2m.qChk (elemsT QA45) (Certificates.OmegaF1051.q0l ()) z0 = true := by
  have h := q2m_check_true
  simp only [Certificates.OmegaQ2m.check, Bool.and_eq_true] at h
  exact h

theorem exists_conj_tA_z0 :
    ∃ c ∈ QP45.originalSubgroup, c * Pk.tA * c⁻¹ = z0 := by
  have h := q2m_parts.1
  simp only [Certificates.OmegaQ2m.conjChk, List.any_eq_true, decide_eq_true_eq,
    mem_elemsT QP45 QP45_ok] at h
  obtain ⟨c, hc, hcz⟩ := h
  exact ⟨c, hc, hcz⟩

theorem centCount_of_mem_Q32
    {x : P45} (hx : x ∈ Q32) (hsq : x * x = 1) (h1 : x ≠ 1) (hz : x ≠ z0) :
    centCount x = 192 := by
  have h := q2m_parts.2
  simp only [Certificates.OmegaQ2m.qChk, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq] at h
  rcases h x (mem_Q32_iff.1 hx) with ((h2 | h2) | h2) | h2
  · exact absurd hsq h2
  · exact absurd h2 h1
  · exact absurd h2 hz
  · exact h2

end CFSG.OddStandard.SmallF3.Omega
