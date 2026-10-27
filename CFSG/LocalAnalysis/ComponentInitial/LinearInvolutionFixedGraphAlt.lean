module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphTools
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module

variable {n : ℕ} {K : Type*} [Field K]

theorem exists_fixed_perfect_even_conjAut_dualAut_of_transpose_eq_neg (hK : ringChar K ≠ 2)
    (h4 : ∃ s : Finset K, s.card = 4) (hn : 3 ≤ n) (A : GL (Fin n) K)
    (hA : (A : Matrix (Fin n) (Fin n) K)ᵀ = -A) :
    ∃ P : Subgroup (projectiveSL n K), Group.IsPerfect P ∧ Even (Nat.card P) ∧
      ∀ s ∈ P, (conjAut n K A * dualAut n K) s = s := by
  classical
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  set R := ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hR
  have hAR : (A : Matrix (Fin n) (Fin n) K) * R = 1 := by
    rw [hR, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRt : Rᵀ = -R := by
    have h1 : Rᵀ * (A : Matrix (Fin n) (Fin n) K)ᵀ = 1 := by
      rw [← transpose_mul, hR, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]
    rw [hA, Matrix.mul_neg, neg_eq_iff_eq_neg] at h1
    calc Rᵀ = Rᵀ * ((A : Matrix (Fin n) (Fin n) K) * R) := by rw [hAR, Matrix.mul_one]
      _ = -R := by rw [← Matrix.mul_assoc, h1, Matrix.neg_mul, Matrix.one_mul]
  have hBalt : (toBilin' R).IsAlt := fun v => by
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    rw [Matrix.toBilin'_apply']
    have hx : v ⬝ᵥ (R *ᵥ v) = -(v ⬝ᵥ (R *ᵥ v)) := by
      conv_lhs => rw [dotProduct_mulVec, ← mulVec_transpose, hRt, neg_mulVec, neg_dotProduct,
        dotProduct_comm]
    have h3 : (2 : K) * (v ⬝ᵥ (R *ᵥ v)) = 0 := by linear_combination hx
    exact (mul_eq_zero.1 h3).resolve_left h2
  have hBnd : (toBilin' R).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2
      (Matrix.isUnits_det_units A⁻¹).ne_zero
  obtain ⟨k, b, hb⟩ := hBalt.exists_basis_toMatrix_eq_J hBnd
  have hk : n = k + k := by
    have h := Module.finrank_eq_card_basis b
    rwa [finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h
  obtain ⟨k', rfl⟩ : ∃ k', k = 2 + k' := ⟨k - 2, by omega⟩
  let Y : SpecialLinearGroup (Fin 2) K →* GL (Fin (2 + k') ⊕ Fin (2 + k')) K :=
    (TauCeti.GLSymplectic (Fin (2 + k')) K).subtype.comp
      (TauCeti.GLSymplectic.leviHom.comp ((blockGL K 2 k').comp SpecialLinearGroup.toGL))
  refine exists_fixed_perfect_even_conjAut_dualAut_of_basis A b Y (fun h => ?_)
    (QuaternionMatrices.slQuatI K) QuaternionMatrices.slQuatI_pow_four ?_
  · rw [hb]
    exact TauCeti.GLSymplectic.mem_iff'.1 (TauCeti.GLSymplectic.leviHom _).2
  · intro c hc
    have hne : (Sum.inl (finSumFinEquiv (Sum.inl 1)) : Fin (2 + k') ⊕ Fin (2 + k')) ≠
        Sum.inl (finSumFinEquiv (Sum.inl 0)) := by
      simp
    have h1 := congrFun (congrFun hc (Sum.inl (finSumFinEquiv (Sum.inl 1))))
      (Sum.inl (finSumFinEquiv (Sum.inl 0)))
    change (((TauCeti.GLSymplectic.leviHom (blockGL K 2 k'
      (SpecialLinearGroup.toGL (QuaternionMatrices.slQuatI K))) :
        TauCeti.GLSymplectic (Fin (2 + k')) K) : GL (Fin (2 + k') ⊕ Fin (2 + k')) K) :
          Matrix (Fin (2 + k') ⊕ Fin (2 + k')) (Fin (2 + k') ⊕ Fin (2 + k')) K) _ _ = _ at h1
    rw [TauCeti.GLSymplectic.coe_leviHom, fromBlocks_apply₁₁, blockGL_apply_inl, scalar_apply,
      diagonal_apply_ne _ hne] at h1
    change QuaternionMatrices.quatI K 1 0 = 0 at h1
    simp [QuaternionMatrices.quatI] at h1

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
