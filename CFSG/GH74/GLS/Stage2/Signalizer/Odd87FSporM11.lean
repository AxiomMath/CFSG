module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSpor
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Glue
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Spec
public import CFSG.LocalAnalysis.OddStandard.MathieuInvolution
public import Certificates.Certificate5161

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Sporadic.Schreier CFSG.OddStandard CFSG.Certificates CFSG.Sporadic.Mathieu

theorem m11_F3S :
    ∀ p ∈ [3, 5, 11], F3S NativeSporadic.M11 (m11InvReps.getD 0 1) p := by
  have hn : (11 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m11Certificate := m11Certificate_check.1
  have hgG : ∀ g ∈ [m11gA, m11gB],
      g ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]
    intro g hg
    rcases List.mem_pair.1 hg with rfl | rfl
    · exact m11a.2
    · exact m11b.2
  have hrows : Certificates.Odd87F3.rowsOK 11 m11Certificate
      [m11gA, m11gB] (m11InvReps.getD 0 1)
      Certificates.Odd87F3.M11.rows = true := Certificates.certificate5161
  intro p hp
  have key : ∀ r ∈ Certificates.Odd87F3.M11.rows, r.prime.Prime →
      F3S NativeSporadic.M11 (m11InvReps.getD 0 1) r.prime := by
    intro r hr hrp
    rw [← m11Certificate_originalSubgroup]
    exact f3S_of_rowsOK hn m11Certificate hQ hgG hrows hr hrp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact key ⟨3, 2, 495, Certificates.Odd87F3.M11.oddWords⟩ (by simp [Certificates.Odd87F3.M11.rows])
      (by norm_num)
  · exact key ⟨5, 1, 495, Certificates.Odd87F3.M11.oddWords⟩ (by simp [Certificates.Odd87F3.M11.rows])
      (by norm_num)
  · exact key ⟨11, 1, 495, []⟩ (by simp [Certificates.Odd87F3.M11.rows]) (by norm_num)

theorem sporKL_M11 :
    SporKL .M11 := by
  intro Y _ _ hY p α Xh h
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥NativeSporadic.M11 := e
  have hcenter : Subgroup.center ↥NativeSporadic.M11 = ⊥ := m11_center_eq_bot'
  have hcard : Nat.card (MulAut ↥NativeSporadic.M11) ≤ Nat.card ↥NativeSporadic.M11 :=
    m11_mulAut_card
  have hrec := m11_innerRecordsValid
  have hF : ∀ p ∈ [3, 5, 11], ∀ t ∈ NativeSporadic.M11, orderOf t = 2 →
      F3S NativeSporadic.M11 t p := by
    intro p hp t ht ho
    refine F3S.of_cover (N := NativeSporadic.M11) (P := fun t => t ∈ NativeSporadic.M11)
      [m11InvReps.getD 0 1] ?_ ?_ t ht ho
    · intro u hu hu2
      obtain ⟨r, hr, c, hc, hur⟩ := hrec.2.2 u hu hu2
      simp only [m11Records, List.mem_singleton] at hr
      subst hr
      exact ⟨m11InvReps.getD 0 1, List.mem_singleton_self _, c, hc, hur⟩
    · intro r hr
      rw [List.mem_singleton] at hr
      subst hr
      exact m11_F3S p hp
  refine QuotCfg.false_of_F3_all e' (ps := [3, 5, 11]) ?_ ?_ h
  · intro β hβ2 q hq
    have hq' : q.Prime ∧ q ≠ 2 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> norm_num
    have hin : β ∈ inner ↥NativeSporadic.M11 := by
      by_contra hn
      exact outer_vacuous_of_card_le hcenter hcard β hn
    obtain ⟨g, hg⟩ := hin
    exact F3.of_inner hq'.1 hq'.2 hcenter (hF q hq) hg.symm hβ2
  · intro q hq hq2 hd
    rw [m11_card] at hd
    have := prime_mem_of_dvd (by norm_num : (7920 : ℕ) ≠ 0)
      (by norm_num : Nat.primeFactorsList 7920 = [2, 2, 2, 2, 3, 3, 5, 11]) hq hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    omega

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
