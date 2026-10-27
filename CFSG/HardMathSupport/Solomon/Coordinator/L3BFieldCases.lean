module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3ABridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.GH74.GLS.IVK

theorem l3bf_normalize {Y P : Type*} [Group Y] [Group P] (e : (Y ⧸ Subgroup.center Y) ≃* P)
    (α : MulAut Y) (φ γ : MulAut P)
    (h : MulAut.congr e (centerDescend Y α) = γ * φ * γ⁻¹) :
    ∃ e' : (Y ⧸ Subgroup.center Y) ≃* P, MulAut.congr e' (centerDescend Y α) = φ := by
  refine ⟨e.trans γ⁻¹, ?_⟩
  ext x
  have h1 := congrArg (fun τ : MulAut P => τ (γ x)) h
  have h2 : e (centerDescend Y α (e.symm (γ x))) = γ (φ x) := by
    simpa [MulAut.congr_apply] using h1
  simp [MulAut.congr_apply, h2]

theorem l3bf_cases_psl {Y : Type*} [Group Y] {α : MulAut Y} (h : IsFieldAutPSL3 α) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (e : (Y ⧸ Subgroup.center Y) ≃* projectiveSL 3 F)
      (σ : F ≃+* F),
      MulAut.congr e (centerDescend Y α) = fieldAut 3 F σ := by
  obtain ⟨F, _, _, e, σ, γ, hψ⟩ := fieldAutPSL3_data h
  obtain ⟨e', he'⟩ := l3bf_normalize e α _ γ hψ
  exact ⟨F, inferInstance, inferInstance, e', σ, he'⟩

theorem l3bf_cases_psu {Y : Type*} [Group Y] (hY : CFSG.Open.IsQuasisimple Y) {α : MulAut Y}
    (hα : orderOf α = 3) (h : IsFieldAutPSU3 α) :
    ∃ (p f f₀ : ℕ) (K : Type) (_ : Field K) (hK : UnitaryFieldData p f K)
      (e : (Y ⧸ Subgroup.center Y) ≃* unitaryPSU hK 3) (σ : K ≃+* K) (_ : orderOf σ = 3)
      (_ : f = 3 * f₀) (_ : UnitaryFieldData p f₀ (fixedField σ)),
      MulAut.congr e (centerDescend Y α) = psuField hK σ := by
  obtain ⟨p, f, K, _, hK, e, σ, γ, -, hψ⟩ := fieldAutPSU3_data h
  obtain ⟨e', he'⟩ := l3bf_normalize e α _ γ hψ
  have hα3 : α ^ 3 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : (MulAut.congr e' (centerDescend Y α)) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, hα3, map_one, map_one]
    rw [he', ← map_pow] at h1
    have h2 : psuField hK (σ ^ 3) ∈ (psuConj hK).range := by rw [h1]; exact one_mem _
    exact psuField_mem_range_psuConj_iff.1 h2
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1, map_one] at he'
    have h2 : centerDescend Y α = 1 := by
      apply (MulAut.congr e').injective
      rw [he', map_one]
    have h3 := eq_one_of_centerDescend_eq_one hY h2
    rw [h3, orderOf_one] at hα
    exact absurd hα (by norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three hK hσ
  exact ⟨p, f, f₀, K, inferInstance, hK, e', σ, hσ, hf, ⟨hK.prime, hf₀, hcard⟩, he'⟩

end CFSG.HardMathSupport.Solomon.Coordinator
