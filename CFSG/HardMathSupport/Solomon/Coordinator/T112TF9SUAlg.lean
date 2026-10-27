module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TF9Spec
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Base

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.GLS.Stage2.Bender.Thm1

section Alg

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def twU (σ : K ≃+* K) (A : U3U h) : ℕ → U3U h
  | 0 => 1
  | k + 1 => twU σ A k * primeFormFieldU h (isPrimeFormGram_one (n := 3)) (σ ^ k) A

theorem coe_twU (σ : K ≃+* K) (A : U3U h) (k : ℕ) :
    ((twU h σ A k : U3U h) : GL (Fin 3) K) =
      CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.twistedProd σ (A : GL (Fin 3) K) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.twistedProd_succ, ← ih]
    rfl

theorem pow_conj_mul_field (σ : K ≃+* K) (A : U3U h) (k : ℕ) :
    (primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) A *
        primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ) ^ k =
      primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) (twU h σ A k) *
        primeFormFieldHom h (isPrimeFormGram_one (n := 3)) (σ ^ k) := by
  induction k with
  | zero => simp [twU]
  | succ k ih =>
    have hc := primeFormField_conj_eq h (isPrimeFormGram_one (n := 3)) (σ ^ k) A
    have hc' : primeFormFieldHom h (isPrimeFormGram_one (n := 3)) (σ ^ k) *
        primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) A =
        primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
          (primeFormFieldU h (isPrimeFormGram_one (n := 3)) (σ ^ k) A) *
        primeFormFieldHom h (isPrimeFormGram_one (n := 3)) (σ ^ k) := by
      rw [← hc]; group
    rw [pow_succ _ k, ih, mul_assoc, ← mul_assoc (primeFormFieldHom h _ (σ ^ k)), hc', twU]
    simp only [map_mul, pow_succ σ k]
    group

theorem exists_conj_realization [Finite K] (hF : Nat.card K = (p ^ f) ^ 2)
    (hU : UnitaryH90 K (p ^ f)) (hq3 : ¬(3 = 3 ∧ p ^ f = 2)) (α : MulAut (U3T h))
    (hα : α ^ 3 = 1)
    (hσ : primeFormFieldFactor h (isPrimeFormGram_one (n := 3)) (le_refl 3) hq3 α ≠ 1) :
    ∃ M : U3U h, α = primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) M *
        primeFormFieldHom h (isPrimeFormGram_one (n := 3))
          (primeFormFieldFactor h (isPrimeFormGram_one (n := 3)) (le_refl 3) hq3 α) *
        (primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) M)⁻¹ := by
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  set c := primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hc
  set fh := primeFormFieldHom h hC with hfh
  set Θ := primeFormFieldFactor h hC (le_refl 3) hq3 with hΘ
  obtain ⟨⟨A, σ⟩, hAσ⟩ := primeFormPsi_surjective h hC (le_refl 3) hq3 α
  have hΘα : Θ α = σ := by rw [← hAσ, primeFormFieldFactor_psi]
  rw [primeFormPsi_apply] at hAσ
  rw [hΘα] at hσ ⊢
  have hσ3 : σ ^ 3 = 1 := by
    have := congrArg Θ hα
    rw [map_pow, map_one, hΘα] at this
    exact this
  have hpow := pow_conj_mul_field h σ A 3
  rw [hAσ] at hpow
  have hα3 : c (twU h σ A 3) * fh (σ ^ 3) = 1 := by rw [← hpow]; exact hα
  rw [hσ3, map_one, mul_one] at hα3
  obtain ⟨d0, hd0⟩ := (u3_conj_eq_one_iff h (twU h σ A 3)).1 hα3
  have hAu : (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map (· ^ (p ^ f)))ᵀ *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have : (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (1 : Matrix (Fin 3) (Fin 3) K) *
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := mem_primeFormUnitary.1 A.2
    rw [Matrix.mul_one] at this
    exact this
  obtain ⟨M, d, hMu, hMd⟩ := hU hF σ (A : GL (Fin 3) K) hσ3 hσ hAu
    ⟨d0, by rw [← coe_twU]; exact hd0⟩
  have hMU : M ∈ U3U h := by
    rw [mem_primeFormUnitary]
    change ((M : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (1 : Matrix (Fin 3) (Fin 3) K) *
        (M : Matrix (Fin 3) (Fin 3) K) = 1
    rw [Matrix.mul_one]
    exact hMu
  set M' : U3U h := ⟨M, hMU⟩ with hM'
  refine ⟨M', ?_⟩
  set σM := primeFormFieldU h hC σ M' with hσM
  have hD : c (A * σM * M'⁻¹) = 1 := by
    refine (u3_conj_eq_one_iff h _).2 ⟨d, ?_⟩
    change (A : GL (Fin 3) K) * (σM : GL (Fin 3) K) * (M : GL (Fin 3) K)⁻¹ = _
    have : (σM : GL (Fin 3) K) = GeneralLinearGroup.map (σ : K →+* K) M := Units.ext rfl
    rw [this, hMd]
    group
  have hcA : c A = c M' * (c σM)⁻¹ := by
    rw [map_mul, map_mul, map_inv] at hD
    rw [← mul_inv_eq_one, ← hD]
    group
  have hconj := primeFormField_conj_eq h hC σ M'⁻¹
  have e1 : c (primeFormFieldU h hC σ M'⁻¹) = (c σM)⁻¹ := by rw [map_inv, map_inv]
  rw [e1, map_inv c M'] at hconj
  have e2 : fh σ * (c M')⁻¹ = (c σM)⁻¹ * fh σ := mul_inv_eq_iff_eq_mul.1 hconj
  rw [← hAσ, hcA, mul_assoc (c M') (fh σ), e2, mul_assoc]

end Alg

end CFSG.HardMathSupport.Solomon.Coordinator
