module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSpor
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Model
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Spec
public import CFSG.LocalAnalysis.OddStandard.MathieuInvolution
public import Certificates.Certificate5162

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Sporadic.Schreier CFSG.OddStandard CFSG.Certificates CFSG.Sporadic.Mathieu

theorem m23_F3S :
    ∀ p ∈ [3, 5, 7, 11, 23], F3S NativeSporadic.M23 (m23InvReps.getD 0 1) p := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  have hrows : Certificates.Odd87F3.rowsOK 23 m23Certificate [m23PermA, m23PermB]
      (m23InvReps.getD 0 1) Certificates.Odd87F3.M23.rows = true := Certificates.certificate5162
  have := f3S_of_rowsOK_primes hn m23Certificate hQ m23_gens_mem hrows (ps := [3, 5, 7, 11, 23])
    (by decide) (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                    rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num)
  rw [m23Certificate_originalSubgroup] at this
  exact this

theorem sporKL_M23 :
    SporKL .M23 := by
  intro Y _ _ hY p α Xh h
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥NativeSporadic.M23 := e
  have hrec := m23_innerRecordsValid
  refine false_of_F3_inner_model NativeSporadic.M23 e' m23_center_eq_bot' m23_mulAut_card
    [m23InvReps.getD 0 1] ?_ (ps := [3, 5, 7, 11, 23]) ?_ ?_ ?_ h
  · intro u hu hu2
    obtain ⟨r, hr, c, hc, hur⟩ := hrec.2.2 u hu hu2
    simp only [m23Records, List.mem_singleton] at hr
    subst hr
    exact ⟨m23InvReps.getD 0 1, List.mem_singleton_self _, c, hc, hur⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro q hq hq2 hd
    rw [m23_card] at hd
    have := prime_mem_of_dvd (by norm_num : (10200960 : ℕ) ≠ 0)
      (by norm_num : Nat.primeFactorsList 10200960 = [2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 7, 11, 23]) hq hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    omega
  · intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    exact m23_F3S

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
