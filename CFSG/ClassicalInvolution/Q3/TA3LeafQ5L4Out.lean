module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4Gen
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabAut

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5L4

open CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

variable {K : Type} [Field K] [Fintype K]

theorem eq_one_of_conjAut_mul_fieldAut_mem_inner (C : GL (Fin 4) K) (τ : K ≃+* K)
    (h : conjAut 4 K C * fieldAut 4 K τ ∈ inner (projectiveSL 4 K)) : τ = 1 := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', rfl⟩ := proj_surjective 4 K g
  rw [← conjAut_toGL] at hg
  have h1 : conjAut 4 K ((Matrix.SpecialLinearGroup.toGL g')⁻¹ * C) * fieldAut 4 K τ = 1 := by
    rw [map_mul, map_inv, mul_assoc, ← hg, inv_mul_cancel]
  exact (eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ h1).1

theorem fieldAut_eq_one_of_pow_four_mem_inner {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ f) (hf : Odd f) (A : GL (Fin 4) K) (σ : K ≃+* K) {ε : ℕ}
    (hε : ε ≤ 1)
    (h : (conjAut 4 K A * fieldAut 4 K σ * dualAut 4 K ^ ε) ^ 4 ∈ inner (projectiveSL 4 K)) :
    σ = 1 := by
  obtain ⟨B, hB⟩ := StabL.sq_eq_conjAut_mul_fieldAut A σ hε
  obtain ⟨C, hC⟩ := StabL.conjAut_mul_fieldAut_pow B (σ ^ 2) 2
  have e4 : (conjAut 4 K A * fieldAut 4 K σ * dualAut 4 K ^ ε) ^ 4 =
      conjAut 4 K C * fieldAut 4 K (σ ^ 4) := by
    rw [show (conjAut 4 K A * fieldAut 4 K σ * dualAut 4 K ^ ε) ^ 4 =
      ((conjAut 4 K A * fieldAut 4 K σ * dualAut 4 K ^ ε) ^ 2) ^ 2 by rw [← pow_mul], hB, hC,
      ← pow_mul]
  rw [e4] at h
  have h4 := eq_one_of_conjAut_mul_fieldAut_mem_inner C _ h
  have hσf : σ ^ f = 1 := by
    rw [← (card_ringAut_and_isCyclic hp K hK).1]
    exact pow_card_eq_one'
  have hcop : Nat.gcd 4 f = 1 := by
    have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hf)
    simpa using this
  have := pow_gcd_eq_one.2 ⟨h4, hσf⟩
  rwa [hcop, pow_one] at this

omit [Fintype K] in
theorem sq_conjAut_mul_dualAut_mem_inner (A : GL (Fin 4) K) :
    (conjAut 4 K A * dualAut 4 K) ^ 2 ∈ inner (projectiveSL 4 K) := by
  obtain ⟨-, -, -, -, hδc, -⟩ := standard_automorphism_transport (K := K) (n := 4)
  have h : (conjAut 4 K A * dualAut 4 K) ^ 2 =
      conjAut 4 K (A * Matrix.GeneralLinearGroup.inverseTranspose A) := by
    rw [sq, map_mul, ← hδc A]
    simp only [mul_assoc]
  rw [h]
  exact LinearOut.conjAut_mem_range_of_det _ 1 (by
    rw [map_mul, LinearOut.det_inverseTranspose', mul_inv_cancel, one_pow])

omit [Fintype K] in
theorem commutator_conjAut_mem_inner (A B : GL (Fin 4) K) :
    ⁅conjAut 4 K A, conjAut 4 K B⁆ ∈ inner (projectiveSL 4 K) := by
  rw [← map_commutatorElement]
  exact LinearOut.conjAut_mem_range_of_det _ 1 (by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _), one_pow])

theorem noQ8Outer_projectiveSL {p f : ℕ} (hp : p.Prime) (hK : Nat.card K = p ^ f)
    (hf : Odd f) :
    ∀ φ : QuaternionGroup 2 →* Outer (projectiveSL 4 K), ¬ Function.Injective φ := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 4) (by norm_num)
  have hlin : ∀ α : MulAut (projectiveSL 4 K), α ^ 4 ∈ inner (projectiveSL 4 K) →
      α ^ 2 ∉ inner (projectiveSL 4 K) → ∃ A : GL (Fin 4) K, α = conjAut 4 K A := by
    intro α h4 h2
    obtain ⟨A, σ, ε, hε, rfl⟩ := hgen α
    have hσ := fieldAut_eq_one_of_pow_four_mem_inner hp hK hf A σ hε h4
    subst hσ
    rw [map_one, mul_one] at h2 ⊢
    interval_cases ε
    · exact ⟨A, by rw [pow_zero, mul_one]⟩
    · rw [pow_one] at h2
      exact absurd (sq_conjAut_mul_dualAut_mem_inner A) h2
  refine noQ8Outer_of_commutator fun α β hα4 hβ4 hα2 hβ2 => ?_
  obtain ⟨A, rfl⟩ := hlin α hα4 hα2
  obtain ⟨B, rfl⟩ := hlin β hβ4 hβ2
  exact commutator_conjAut_mem_inner A B

end CFSG.ClassicalInvolution.Q3.TA3.Q5L4
