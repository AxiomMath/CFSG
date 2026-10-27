module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4M2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOFCfg
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4Adm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4N4

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local BS4 BL4
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K]

theorem not_btConfig_u4 {k : Kind} (hk : IsClassicalKind k) (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) : ¬ BTConfig k p (hypPSU h 2 0) := by
  rintro ⟨W, I, Q, U, hW, hWp, hI, hIW, hQI, hQ, hU, hUW, hUI, hadm⟩
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K p] at h0'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp h0')
  have hIne : I ≠ ⊥ := by
    rintro rfl
    have h4 := hQ.2
    rw [le_bot_iff.mp hQI, Subgroup.card_bot] at h4
    norm_num at h4
  obtain ⟨N, hN0, hNt, hNlin, hNsemi⟩ := exists_subspace hp2 hW hWp
  obtain ⟨hd1, hd2, g, hg⟩ := exists_smul_hypFlag_eq (h := h) (by norm_num) hN0 hNt
  have hIN : ∀ s ∈ I.comap (hypProj h 2 0), ∀ v ∈ N,
      (((s : hypSU h 2 0) : GL (HypIndex 2 0) K) : MH K) *ᵥ v ∈ N := fun s hs =>
    hNlin _ (mem_normalizer_preGL_of_proj fun w hw =>
      (Subgroup.mem_normalizer_iff.mp (hIW hs) w).mp hw)
  have hS : ∀ u ∈ U, u ≠ 1 → u * u = 1 → SurvU4Orth h u := fun u hu hu1 huu =>
    survU4Orth_of_admAut hk h hp2 huu (hadm u hu hu1)
  rcases (show Module.finrank K N = 1 ∨ Module.finrank K N = 2 by omega) with hd | hd
  · rw [hd] at hg
    exact false_of_point_u4 h h2 hI hQI hQ hg hIN
  · rw [hd] at hg
    exact false_of_lagr_u4 h h2 hI hIne hU hUW hUI hS hg hIN hNlin hNsemi

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
