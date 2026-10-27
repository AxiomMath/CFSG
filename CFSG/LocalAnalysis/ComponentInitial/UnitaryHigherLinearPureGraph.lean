module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherCharTwoOrthonormal
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphTools

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix Module LinearFlag
open LinearMap (BilinForm)
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (exists_symplectic_basis)

variable {K : Type} [Field K] {n : ℕ}

@[expose] def blockSwapJ (n r : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if (j : ℕ) = i + r ∨ (i : ℕ) = j + r then 1 else 0

theorem exists_congruence_of_basis (A : GL (Fin n) K) (b : Basis (Fin n) K (Fin n → K)) :
    ∃ H C : GL (Fin n) K,
      (C : Matrix (Fin n) (Fin n) K) =
        BilinForm.toMatrix b (Matrix.toBilin' (A : Matrix (Fin n) (Fin n) K)) ∧
      (A : Matrix (Fin n) (Fin n) K) = H * C * (H : Matrix (Fin n) (Fin n) K)ᵀ ∧
      conjAut n K A * dualAut n K =
        conjAut n K H * (conjAut n K C * dualAut n K) * (conjAut n K H)⁻¹ := by
  obtain ⟨Q, hQ⟩ : ∃ Q : GL (Fin n) K,
      (Q : Matrix (Fin n) (Fin n) K) = (Pi.basisFun K (Fin n)).toMatrix b :=
    ⟨⟨_, _, (Pi.basisFun K (Fin n)).toMatrix_mul_toMatrix_flip b,
      b.toMatrix_mul_toMatrix_flip (Pi.basisFun K (Fin n))⟩, rfl⟩
  have hQQ : (Q : Matrix (Fin n) (Fin n) K) * ((Q⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hCval : ((GeneralLinearGroup.inverseTranspose Q⁻¹ * A * Q : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
        (Q : Matrix (Fin n) (Fin n) K)ᵀ * A * (Q : Matrix (Fin n) (Fin n) K) := by
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_inverseTranspose, inv_inv]
  refine ⟨GeneralLinearGroup.inverseTranspose Q, GeneralLinearGroup.inverseTranspose Q⁻¹ * A * Q,
    ?_, ?_, ?_⟩
  · rw [hCval, hQ, ← BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun K (Fin n)) b,
      BilinForm.toMatrix_basisFun, BilinForm.toMatrix'_toBilin']
  · rw [hCval, GeneralLinearGroup.coe_inverseTranspose, transpose_transpose]
    have h1 : ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
        (Q : Matrix (Fin n) (Fin n) K)ᵀ = 1 := by
      rw [← transpose_mul, hQQ, transpose_one]
    calc (A : Matrix (Fin n) (Fin n) K)
        = (((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
            (Q : Matrix (Fin n) (Fin n) K)ᵀ) * A *
              ((Q : Matrix (Fin n) (Fin n) K) * ((Q⁻¹ : GL (Fin n) K) :
                Matrix (Fin n) (Fin n) K)) := by
          rw [h1, hQQ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  · have hiT : GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.inverseTranspose Q)⁻¹ =
        Q⁻¹ := by
      rw [← map_inv, GeneralLinearGroup.inverseTranspose_inverseTranspose]
    have hHCA : GeneralLinearGroup.inverseTranspose Q *
        (GeneralLinearGroup.inverseTranspose Q⁻¹ * A * Q) *
          GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.inverseTranspose Q)⁻¹ = A := by
      rw [hiT]
      calc GeneralLinearGroup.inverseTranspose Q *
            (GeneralLinearGroup.inverseTranspose Q⁻¹ * A * Q) * Q⁻¹
          = (GeneralLinearGroup.inverseTranspose Q * GeneralLinearGroup.inverseTranspose Q⁻¹) *
              A * (Q * Q⁻¹) := by group
        _ = A := by rw [← map_mul, mul_inv_cancel, map_one, one_mul, mul_one]
    calc conjAut n K A * dualAut n K
        = conjAut n K (GeneralLinearGroup.inverseTranspose Q *
            (GeneralLinearGroup.inverseTranspose Q⁻¹ * A * Q) *
              GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.inverseTranspose Q)⁻¹) *
                dualAut n K := by rw [hHCA]
      _ = conjAut n K (GeneralLinearGroup.inverseTranspose Q) *
            conjAut n K (GeneralLinearGroup.inverseTranspose Q⁻¹ * A * Q) *
              (conjAut n K (GeneralLinearGroup.inverseTranspose
                (GeneralLinearGroup.inverseTranspose Q)⁻¹) * dualAut n K) := by
          rw [map_mul, map_mul, mul_assoc]
      _ = conjAut n K (GeneralLinearGroup.inverseTranspose Q) *
            conjAut n K (GeneralLinearGroup.inverseTranspose Q⁻¹ * A * Q) *
              (dualAut n K * conjAut n K (GeneralLinearGroup.inverseTranspose Q)⁻¹) := by
          rw [dualAut_mul_conjAut]
      _ = _ := by
          rw [map_inv (conjAut n K)]
          group

theorem J_apply_eq_blockSwapJ [CharP K 2] {r : ℕ} (h : r + r = n) (x y : Fin r ⊕ Fin r) :
    Matrix.J (Fin r) K x y =
      blockSwapJ n r ((finSumFinEquiv.trans (finCongr h)) x)
        ((finSumFinEquiv.trans (finCongr h)) y) := by
  rcases x with a | a <;> rcases y with c | c <;>
    simp only [blockSwapJ, Matrix.J, Matrix.of_apply, Equiv.trans_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply,
      CharTwo.neg_eq]
  · have h1 : ¬((c : ℕ) = a + r ∨ (a : ℕ) = c + r) := by omega
    simp [h1]
  · by_cases hac : a = c
    · subst hac
      have h2 : r + (a : ℕ) = a + r := by omega
      simp [h2]
    · have h1 : ¬(r + (c : ℕ) = a + r ∨ (a : ℕ) = r + c + r) := by
        intro h2
        exact hac (Fin.ext (by omega))
      simp [hac, h1]
  · by_cases hac : a = c
    · subst hac
      have h2 : r + (a : ℕ) = a + r := by omega
      simp [h2]
    · have h1 : ¬((c : ℕ) = r + a + r ∨ r + (a : ℕ) = c + r) := by
        intro h2
        exact hac (Fin.ext (by omega))
      simp [hac, h1]
  · have h1 : ¬(r + (c : ℕ) = r + a + r ∨ r + (a : ℕ) = r + c + r) := by omega
    simp [h1]

theorem even_linear_pure_graph_involution_normal_forms {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (A : GL (Fin n) K)
    (hα : (conjAut n K A * dualAut n K) ^ 2 = 1) :
    (A : Matrix (Fin n) (Fin n) K)ᵀ = A ∧
    (∃ H C : GL (Fin n) K,
      (A : Matrix (Fin n) (Fin n) K) = H * C * (H : Matrix (Fin n) (Fin n) K)ᵀ ∧
      conjAut n K A * dualAut n K =
        conjAut n K H * (conjAut n K C * dualAut n K) * (conjAut n K H)⁻¹ ∧
      (((C : Matrix (Fin n) (Fin n) K) = 1 ∧
          ¬∀ v : Fin n → K, v ⬝ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) = 0) ∨
        ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r ∧
          ∀ v : Fin n → K, v ⬝ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) = 0)) ∧
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (B : BilinForm K V),
      B.IsSymm → B.Nondegenerate → ¬B.IsAlt →
        ∃ b : Basis (Fin (finrank K V)) K V, ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hsq : ∀ a : K, IsSquare a := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
  have hsym : (A : Matrix (Fin n) (Fin n) K)ᵀ = A := by
    rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut hn A hα with h | h
    · exact h
    · rw [h]
      ext i j
      rw [Matrix.neg_apply, CharTwo.neg_eq]
  have hBsymm : (Matrix.toBilin' (A : Matrix (Fin n) (Fin n) K)).IsSymm := ⟨fun v w => by
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', dotProduct_mulVec, ← mulVec_transpose,
      hsym, dotProduct_comm]⟩
  have hBnd : (Matrix.toBilin' (A : Matrix (Fin n) (Fin n) K)).Nondegenerate :=
    Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_of_det_ne_zero
      ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero)
  refine ⟨hsym, ?_, fun V _ _ _ B hB hnd halt => exists_orthonormal_basis_of_charTwo hsq hB hnd
    (Or.inr (by
      by_contra h
      push Not at h
      exact halt h))⟩
  by_cases halt : ∀ v : Fin n → K, v ⬝ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) = 0
  · have hBalt : (Matrix.toBilin' (A : Matrix (Fin n) (Fin n) K)).IsAlt := fun v => by
      rw [Matrix.toBilin'_apply']
      exact halt v
    obtain ⟨m, b, hd, hb⟩ := exists_symplectic_basis _ hBalt hBnd
    rw [Module.finrank_fin_fun] at hd
    have hmm : m + m = n := by omega
    obtain ⟨H, C, hC, hA, hconj⟩ :=
      exists_congruence_of_basis A (b.reindex (finSumFinEquiv.trans (finCongr hmm)))
    refine ⟨H, C, hA, hconj, Or.inr ⟨m, hd, ?_, halt⟩⟩
    rw [hC]
    ext i j
    obtain ⟨x, rfl⟩ := (finSumFinEquiv.trans (finCongr hmm)).surjective i
    obtain ⟨y, rfl⟩ := (finSumFinEquiv.trans (finCongr hmm)).surjective j
    rw [BilinForm.toMatrix_apply, Basis.reindex_apply, Basis.reindex_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply, ← BilinForm.toMatrix_apply, hb, J_apply_eq_blockSwapJ hmm]
  · push Not at halt
    obtain ⟨x, hx⟩ := halt
    obtain ⟨b, hb⟩ := exists_orthonormal_basis_of_charTwo hsq hBsymm hBnd
      (Or.inr ⟨x, by rw [Matrix.toBilin'_apply']; exact hx⟩)
    obtain ⟨H, C, hC, hA, hconj⟩ :=
      exists_congruence_of_basis A (b.reindex (finCongr (Module.finrank_fin_fun K)))
    refine ⟨H, C, hA, hconj, Or.inl ⟨?_, fun h => hx (h x)⟩⟩
    rw [hC]
    ext i j
    rw [BilinForm.toMatrix_apply, Basis.reindex_apply, Basis.reindex_apply, hb, Matrix.one_apply]
    simp only [(finCongr (Module.finrank_fin_fun K)).symm.injective.eq_iff]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
