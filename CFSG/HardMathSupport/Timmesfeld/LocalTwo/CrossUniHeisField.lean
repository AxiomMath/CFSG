module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalOuter

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem tau_fixes_of_commute (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {A B : primeFormUnitary h (idGram K n)} {c : Kˣ}
    (hAB : (A : GL (Fin n) K) * B = B * A * GeneralLinearGroup.scalar (Fin n) c)
    {M' : primeFormUnitary h (idGram K n)} {τ : K ≃+* K}
    (hgA : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M', τ⟩ *
        primeFormConjHom h (idGram K n) A = primeFormConjHom h (idGram K n) A *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M', τ⟩)
    (hgB : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M', τ⟩ *
        primeFormConjHom h (idGram K n) B = primeFormConjHom h (idGram K n) B *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M', τ⟩) :
    τ (c : K) = c := by
  haveI : NeZero n := ⟨by omega⟩
  set Ψ := primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M', τ⟩ with hΨ
  obtain ⟨dA, hdA⟩ := exists_scalar_of_commute_conj hn hne hgA
  obtain ⟨dB, hdB⟩ := exists_scalar_of_commute_conj hn hne hgB
  have hmA : idAct' h n hn hne Ψ ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (dA : K) • ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [hdA, scalar_coe_eq_smul_one, Matrix.mul_smul, Matrix.mul_one]
  have hmB : idAct' h n hn hne Ψ ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (dB : K) • ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [hdB, scalar_coe_eq_smul_one, Matrix.mul_smul, Matrix.mul_one]
  have hmc : idAct' h n hn hne Ψ ((c : K) • (1 : Matrix (Fin n) (Fin n) K)) =
      (τ (c : K)) • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [hΨ, idAct'_psi_apply]
    have e1 : ((c : K) • (1 : Matrix (Fin n) (Fin n) K)).map τ =
        (τ (c : K)) • (1 : Matrix (Fin n) (Fin n) K) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    have e2 : ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((M' : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [e1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, e2]
  have hAB' : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((c : K) • (1 : Matrix (Fin n) (Fin n) K)) := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hAB
    simp only [Units.val_mul, scalar_coe_eq_smul_one] at this
    exact this
  have hφ := congrArg (idAct' h n hn hne Ψ) hAB'
  rw [map_mul, map_mul, map_mul, hmA, hmB, hmc] at hφ
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul] at hφ
  rw [hAB'] at hφ
  simp only [Matrix.mul_smul, Matrix.mul_one, smul_smul] at hφ
  have hunit : IsUnit (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    have := Units.isUnit ((B : GL (Fin n) K) * (A : GL (Fin n) K))
    rwa [Units.val_mul] at this
  have key := smul_matrix_cancel hunit hφ
  have hd : (dA : K) * dB ≠ 0 := mul_ne_zero dA.ne_zero dB.ne_zero
  exact (mul_left_cancel₀ hd (by linear_combination key)).symm

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
