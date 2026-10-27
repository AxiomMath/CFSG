module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4OC
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFStd
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFL4Aut

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open Matrix QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.ModelFacts.Orth15
open CFSG.ClassicalInvolution.Asc77.CX.MF2L (spForm)
open scoped Pointwise

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

local notation "V₈" => Fin 4 ⊕ Fin 4 → GaloisField 3 1

theorem exists_cplx_comm_of_involution {a : V₈ ≃ₗ[𝔽₃] V₈} (hsim : ∀ v, Q₄ (a v) = -1 * Q₄ v)
    (haa : a * a = 1) :
    ∃ y : V₈ ≃ₗ[𝔽₃] V₈, y ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ ∧ (∀ v, y (y v) = -v) ∧
      y * a = a * y := by
  have hK : Nat.card 𝔽₃ = 3 := ModelFacts.TG3.natCard_galoisField_three
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  have hQ := nondegenerate_polarBilin_quadPlus 4 𝔽₃
  obtain ⟨θ, hθO, hθ⟩ := exists_standardizing_n h2 hQ haa (fun v => by rw [hsim, neg_one_mul])
  set B : GL (Fin 4) 𝔽₃ := L4.spFormGL 𝔽₃ with hB
  have hM : (Levi.blockGL B : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) 𝔽₃) * Levi.blockGL B = -1 := by
    rw [Levi.blockGL_val, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    have hi : ((B⁻¹ : GL (Fin 4) 𝔽₃) : Matrix (Fin 4) (Fin 4) 𝔽₃) = -spForm 1 1 := rfl
    rw [hi, ← Matrix.transpose_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, hB, L4.coe_spFormGL,
      L4.spForm_mul_self, Matrix.transpose_neg, Matrix.transpose_one, ← fromBlocks_one,
      fromBlocks_neg, neg_zero]
  set y₀ := glLin (Levi.blockGL B) with hy₀
  have hy₀2 : ∀ v, y₀ (y₀ v) = -v := fun v => by
    rw [← LinearEquiv.mul_apply, ← map_mul, glLin_apply, Units.val_mul, hM, Matrix.neg_mulVec,
      Matrix.one_mulVec]
  have hy₀O : y₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [hy₀, glLin_apply]
    exact Levi.quadPlus_blockGL B v
  have hy₀a₀ : y₀ * Levi.a₀ 𝔽₃ 4 = Levi.a₀ 𝔽₃ 4 * y₀ := by
    rw [hy₀, Levi.a₀, ← map_mul, ← map_mul, Levi.blockGL_mul_a₀GL]
  refine ⟨θ * y₀ * θ⁻¹, mul_mem (mul_mem hθO hy₀O) (inv_mem hθO), fun v => ?_, ?_⟩
  · simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, hy₀2,
      map_neg, LinearEquiv.apply_symm_apply]
  · have h1 : θ⁻¹ * a * θ = Levi.a₀ 𝔽₃ 4 := by
      rw [mul_assoc, hθ, ← mul_assoc, inv_mul_cancel, one_mul]
    calc θ * y₀ * θ⁻¹ * a = θ * (y₀ * (θ⁻¹ * a * θ)) * θ⁻¹ := by group
      _ = θ * (Levi.a₀ 𝔽₃ 4 * y₀) * θ⁻¹ := by rw [h1, hy₀a₀]
      _ = θ * ((θ⁻¹ * a * θ) * y₀) * θ⁻¹ := by rw [h1]
      _ = a * (θ * y₀ * θ⁻¹) := by group

theorem simFam_neg_one_one : SimFam (-1) 1 := by
  intro a hsim ha2 β hodd hβ
  have hK : Nat.card 𝔽₃ = 3 := ModelFacts.TG3.natCard_galoisField_three
  have haa : a * a = 1 := LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, ha2, one_smul]
    rfl
  obtain ⟨y, hyO, hy2, hya⟩ := exists_cplx_comm_of_involution hsim haa
  have hmem := mem_commutator_of_sq_neg_one hK (nondegenerate_polarBilin_quadPlus 4 𝔽₃)
    finrank_d4 hyO hy2
  have hΩ := symm_mem_statedOmega hmem
  have hE : y ∈ elementaryGroup Q₄ := by
    rwa [commutator_orthogonalGroup_quadPlus (by norm_num)] at hmem
  obtain ⟨x, hx, hxc⟩ := exists_spin_of_mem_elementary hE hΩ
  refine typeII_smul hK β hodd ⟨_, hΩ⟩ (fun v => ?_) ?_
  · simp only [MulEquiv.apply_symm_apply]
    exact hy2 v
  · rw [← hxc]
    exact hβ x (by rw [hx]; exact hya)

end CFSG.ClassicalInvolution.Q3.TL4
