module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Red
public import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainU
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutModel

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 (r0 exists_conj_r0 sl2_sq_cases sl2_sq_one
  isQuasisimple_sl2)
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (isQuasisimple_of_equiv)
open scoped MatrixGroups

section SU2

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su2_sq_cases (h2 : (2 : K) ≠ 0) (A : Su K p f 2) {μ : K}
    (h : suMat A * suMat A = μ • (1 : Matrix (Fin 2) (Fin 2) K)) :
    (μ = 1 ∧ (suMat A = 1 ∨ suMat A = -1)) ∨ (μ = -1 ∧ suMat A * suMat A = -1) :=
  sl2_sq_cases h2 ⟨suMat A, det_suMat A⟩ h

theorem sl2_neg_one_of_sq_one {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {ν : SL(2, F)}
    (h : ν * ν = 1) (h1 : ν ≠ 1) : ν = -1 := by
  have hm : (ν : Matrix (Fin 2) (Fin 2) F) * ν = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, h, Matrix.SpecialLinearGroup.coe_one]
  rcases sl2_sq_one h2 ν hm with h' | h'
  · exact absurd (Subtype.ext h') h1
  · exact Subtype.ext (by simpa using h')

theorem exists_conj_of_sq_neg {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) {G : Type}
    [Group G] (e : SL(2, F) ≃* G) {ν : G} (hν2 : ν * ν = 1) (hν1 : ν ≠ 1) {A B : G}
    (hA : A * A = ν) (hB : B * B = ν) : ∃ h : G, h * B * h⁻¹ = A := by
  have hν : e.symm ν = -1 := by
    refine sl2_neg_one_of_sq_one h2 ?_ ?_
    · rw [← map_mul, hν2, map_one]
    · intro h
      exact hν1 (e.symm.injective (by rw [h, map_one]))
  have key : ∀ C : G, C * C = ν → ∃ h : SL(2, F), h * r0 * h⁻¹ = e.symm C := by
    intro C hC
    apply exists_conj_r0 h2
    have : e.symm C * e.symm C = -1 := by rw [← map_mul, hC, hν]
    rw [← Matrix.SpecialLinearGroup.coe_mul, this, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨h₁, hh₁⟩ := key A hA
  obtain ⟨h₂, hh₂⟩ := key B hB
  refine ⟨e (h₁ * h₂⁻¹), e.symm.injective ?_⟩
  simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
  rw [← hh₁, ← hh₂]
  group

theorem jSU_mul_self : jSU K p f * jSU K p f = negOneSU K p f := by
  apply suMat_injective
  rw [suMat_mul, suMat_jSU, suMat_negOneSU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_conj_jSU (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0) {A : Su K p f 2}
    (hA : A * A = negOneSU K p f) : ∃ h : Su K p f 2, h * jSU K p f * h⁻¹ = A := by
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_su_two (K := K) (p := p) (f := f) hK
  have h2F : (2 : fixedSubfield K p f) ≠ 0 := by
    intro h
    apply h2
    have e : ((2 : fixedSubfield K p f) : K) = 2 := rfl
    rw [← e, h]
    rfl
  exact exists_conj_of_sq_neg h2F e negOneSU_mul_self (negOneSU_ne_one h2) hA jSU_mul_self

theorem isQuasisimple_su2 (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    CFSG.IsQuasisimple (Su K p f 2) := by
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_su_two (K := K) (p := p) (f := f) hK
  have h4 : 4 ≤ Nat.card (fixedSubfield K p f) := by
    rw [card_fixedSubfield hK]
    omega
  exact isQuasisimple_of_equiv e (isQuasisimple_sl2 h4)

end SU2

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu
