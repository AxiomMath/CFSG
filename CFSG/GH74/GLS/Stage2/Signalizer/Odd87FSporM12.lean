module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSpor
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Model
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Spec
public import Certificates.Certificate5164

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu

theorem m12_outer_cover' :
    ∀ u : Equiv.Perm (Fin 24), m12Sigma⁻¹ * u ∈ m12D.originalSubgroup → orderOf u = 2 →
      ∃ r ∈ [m12Sigma], ∃ c ∈ m12D.originalSubgroup, u = c * r * c⁻¹ := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, -, hord⟩ := m12_sigma_cover
  exact (exists_conj_of_repsOK hn m12D m12D_check.1 (pairTables_spec hn (m12_gens_memD _ (by simp))
    (m12_gens_memD _ (by simp))) m12Sigma
    (inv_conj_mem _ m12D_sigma_normalizes m12D_sigma_sq) (by norm_num) [m12Sigma]
    (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by simp, (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hord⟩)
    1000 hok).1

theorem m12_F3S :
    (∀ r ∈ Certificates.Odd87F3.M12.innerReps, ∀ p ∈ [3, 5, 11], F3S m12D.originalSubgroup r p) ∧
    (∀ p ∈ [3, 5, 11], F3S m12D.originalSubgroup m12Sigma p) ∧
    (∀ u : Equiv.Perm (Fin 24), u ∈ m12D.originalSubgroup → orderOf u = 2 →
      ∃ r ∈ Certificates.Odd87F3.M12.innerReps, ∃ c ∈ m12D.originalSubgroup, u = c * r * c⁻¹) := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m12D := m12D_check.1
  have hall : Certificates.Odd87F3.M12.m12F3OK = true := Certificates.certificate5164
  simp only [Certificates.Odd87F3.M12.m12F3OK, Bool.and_eq_true] at hall
  obtain ⟨⟨⟨hcov, h1⟩, h2⟩, h3⟩ := hall
  have hpr : ∀ p ∈ [3, 5, 11], p.Prime := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num
  have hrows := fun {u : Equiv.Perm (Fin 24)} {rs : List Certificates.Odd87F3.Row}
      (h : Certificates.Odd87F3.rowsOK 24 m12D [m12A1, m12B1] u rs = true)
      (hps : ∀ p ∈ [3, 5, 11], ∃ r ∈ rs, r.prime = p) =>
    f3S_of_rowsOK_primes hn m12D hQ m12_gens_memD h hps hpr
  refine ⟨?_, hrows h3 (by decide), ?_⟩
  · intro r hr p hp
    simp only [Certificates.Odd87F3.M12.innerReps, List.mem_cons, List.not_mem_nil, or_false]
      at hr
    rcases hr with rfl | rfl
    · exact hrows h1 (by decide) p hp
    · exact hrows h2 (by decide) p hp
  · intro u hu hu2
    refine cover_of_coverOK hn m12D hQ (m12_gens_memD _ (by simp)) (m12_gens_memD _ (by simp))
      (g₀ := 1) (by simp) ?_ hcov u (by simpa using hu) hu2
    intro r hr
    simp only [inv_one, one_mul]
    simp only [Certificates.Odd87F3.M12.innerReps, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact evalCodes_mem _ m12_gens_memD _
    · exact evalCodes_mem _ m12_gens_memD _

theorem sporKL_M12 :
    SporKL .M12 := by
  intro Y _ _ hY p α Xh h
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥m12D.originalSubgroup := (e : Y ≃* NativeSporadic.M12).trans m12EquivD
  obtain ⟨hFinn, hFout, hcov⟩ := m12_F3S
  refine false_of_F3_model m12D.originalSubgroup e' m12D_center m12Sigma m12D_sigma_normalizes
    m12D_sigma_sq m12D_sigma_outer m12D_mulAut_card Certificates.Odd87F3.M12.innerReps [m12Sigma]
    hcov m12_outer_cover' (ps := [3, 5, 11]) ?_ ?_ hFinn ?_ h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> norm_num
  · intro q hq hq2 hd
    have hcard : Nat.card m12D.originalSubgroup = 95040 := by
      rw [← m12D.orderCertificate_eq_card m12D_check.1, m12D_check.2]
    rw [hcard] at hd
    have := prime_mem_of_dvd (by norm_num : (95040 : ℕ) ≠ 0)
      (by norm_num : Nat.primeFactorsList 95040 = [2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 11]) hq hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    omega
  · intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    exact hFout

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
