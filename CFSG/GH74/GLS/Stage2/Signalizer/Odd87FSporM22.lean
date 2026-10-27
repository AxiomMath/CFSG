module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSpor
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Model
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Spec
public import CFSG.LocalAnalysis.OddStandard.MathieuInvolution
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer
public import Certificates.Certificate5163

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Sporadic.Schreier CFSG.OddStandard CFSG.Certificates CFSG.Sporadic.Mathieu

theorem m22_outer_cover' :
    ∀ u : Equiv.Perm (Fin 22), m22Delta⁻¹ * u ∈ NativeSporadic.M22 → orderOf u = 2 →
      ∃ r ∈ m22OutReps, ∃ c ∈ NativeSporadic.M22, u = c * r * c⁻¹ := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, -, -⟩ := m22_outer_cover
  obtain ⟨hr1, hro1, -⟩ := m22_out_rep_data1
  obtain ⟨hr2, hro2, -⟩ := m22_out_rep_data2
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hg₀ : ∀ h ∈ m22Certificate.originalSubgroup,
      m22Delta⁻¹ * h * m22Delta ∈ m22Certificate.originalSubgroup := by
    rw [m22Certificate_originalSubgroup]
    exact inv_conj_mem _ m22_delta_normalizes m22_delta_sq
  have hreps : ∀ r ∈ m22OutReps, m22Delta⁻¹ * r ∈ m22Certificate.originalSubgroup ∧ orderOf r = 2 := by
    intro r hr
    rw [m22OutReps_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨hr1, hro1⟩
    · exact ⟨hr2, hro2⟩
  rw [← m22Certificate_originalSubgroup]
  exact (exists_conj_of_repsOK hn m22Certificate hQ (pairTables_spec hn hA hB) m22Delta hg₀
    (by norm_num) m22OutReps hreps 2000 hok).1

theorem m22_F3S :
    (∀ p ∈ [3, 5, 7, 11], F3S NativeSporadic.M22 (m22InvReps.getD 0 1) p) ∧
    (∀ p ∈ [3, 5, 7, 11], F3S NativeSporadic.M22 (m22OutReps.getD 0 1) p) ∧
    (∀ p ∈ [3, 5, 7, 11], F3S NativeSporadic.M22 (m22OutReps.getD 1 1) p) := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  have hall : Certificates.Odd87F3.M22.m22F3OK = true := Certificates.certificate5163
  simp only [Certificates.Odd87F3.M22.m22F3OK, Bool.and_eq_true] at hall
  obtain ⟨⟨h1, h2⟩, h3⟩ := hall
  have hpr : ∀ p ∈ [3, 5, 7, 11], p.Prime := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · have := f3S_of_rowsOK_primes hn m22Certificate hQ m22_gens_mem h1 (ps := [3, 5, 7, 11])
      (by decide) hpr
    rwa [m22Certificate_originalSubgroup] at this
  · have := f3S_of_rowsOK_primes hn m22Certificate hQ m22_gens_mem h2 (ps := [3, 5, 7, 11])
      (by decide) hpr
    rwa [m22Certificate_originalSubgroup] at this
  · have := f3S_of_rowsOK_primes hn m22Certificate hQ m22_gens_mem h3 (ps := [3, 5, 7, 11])
      (by decide) hpr
    rwa [m22Certificate_originalSubgroup] at this

theorem sporKL_M22 :
    SporKL .M22 := by
  intro Y _ _ hY p α Xh h
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥NativeSporadic.M22 := e
  have hrec := m22_innerRecordsValid
  obtain ⟨hF1, hF2, hF3⟩ := m22_F3S
  refine false_of_F3_model NativeSporadic.M22 e' m22_center_eq_bot' m22Delta m22_delta_normalizes
    m22_delta_sq m22_delta_outer (by simpa using m22_mulAut_card) [m22InvReps.getD 0 1] m22OutReps
    ?_ m22_outer_cover' (ps := [3, 5, 7, 11]) ?_ ?_ ?_ ?_ h
  · intro u hu hu2
    obtain ⟨r, hr, c, hc, hur⟩ := hrec.2.2 u hu hu2
    simp only [m22Records, List.mem_singleton] at hr
    subst hr
    exact ⟨m22InvReps.getD 0 1, List.mem_singleton_self _, c, hc, hur⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> norm_num
  · intro q hq hq2 hd
    rw [m22_card] at hd
    have := prime_mem_of_dvd (by norm_num : (443520 : ℕ) ≠ 0)
      (by norm_num : Nat.primeFactorsList 443520 = [2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 7, 11]) hq hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    omega
  · intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    exact hF1
  · intro r hr
    rw [m22OutReps_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hF2
    · exact hF3

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
