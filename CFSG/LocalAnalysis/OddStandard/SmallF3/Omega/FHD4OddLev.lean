module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFLevi
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHD4OddCube
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHD4OddMat
import CFSG.ClassicalInvolution.SmallOrth.Orth3GaussMain

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix QuadraticMap CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open scoped MatrixGroups Pointwise

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

local notation "V₈" => Fin 4 ⊕ Fin 4 → GaloisField 3 1

theorem fh_embSL_sq {F : Type} [Field F] {A : SL(4, F)}
    (hA : (A : Matrix (Fin 4) (Fin 4) F) * A = -1) (v : Fin 4 ⊕ Fin 4 → F) :
    Levi.embSL F 4 A (Levi.embSL F 4 A v) = -v := by
  set B : GL (Fin 4) F := Matrix.SpecialLinearGroup.toGL A with hB
  have hBB : (B : Matrix (Fin 4) (Fin 4) F) * B = -1 := hA
  have hinv : ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      -(B : Matrix (Fin 4) (Fin 4) F) := by
    have h1 : (B : Matrix (Fin 4) (Fin 4) F) * (-(B : Matrix (Fin 4) (Fin 4) F)) = 1 := by
      rw [Matrix.mul_neg, hBB, neg_neg]
    rw [Matrix.coe_units_inv]
    exact Matrix.inv_eq_right_inv h1
  have hM : (Levi.blockGL B : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) * Levi.blockGL B = -1 := by
    rw [Levi.blockGL_val, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [hinv, ← Matrix.transpose_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, hBB,
      Matrix.transpose_neg, Matrix.transpose_one, ← fromBlocks_one, fromBlocks_neg, neg_zero]
  rw [Levi.embSL_apply, ← LinearEquiv.mul_apply, ← map_mul, glLin_apply, Units.val_mul, hM,
    Matrix.neg_mulVec, Matrix.one_mulVec]

theorem fh_mem_elementary_of_perfect {G : Type} [Group G] (hG : Group.IsPerfect G)
    (ρ : G →* (V₈ ≃ₗ[𝔽₃] V₈)) (hρ : ∀ z, ρ z ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄) (z : G) :
    ρ z ∈ elementaryGroup Q₄ := by
  rw [← commutator_orthogonalGroup_quadPlus (by norm_num)]
  exact range_le_commutator hG ρ (by rintro _ ⟨w, rfl⟩; exact hρ w) ⟨z, rfl⟩

theorem fh_embSL_mem_elementary (A : SL(4, 𝔽₃)) : Levi.embSL 𝔽₃ 4 A ∈ elementaryGroup Q₄ := by
  exact fh_mem_elementary_of_perfect
    (CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num))
    (Levi.embSL 𝔽₃ 4) Levi.embSL_mem_orthogonalGroup A

theorem fh_smul_of_conj {a c θ : V₈ ≃ₗ[𝔽₃] V₈} {β : MulAut (D4P 𝔽₃)} (hodd : Odd (orderOf β))
    (hβ : ∀ x : spinGroup Q₄, spinAction Q₄ x * a = a * spinAction Q₄ x →
      Odd (orderOf (Q3T.d4Proj 𝔽₃ x)) → β (Q3T.d4Proj 𝔽₃ x) = Q3T.d4Proj 𝔽₃ x)
    (hθ : θ ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄) (hac : a = θ * c * θ⁻¹)
    (hT : Levi.embSL 𝔽₃ 4 fhLevT * c = c * Levi.embSL 𝔽₃ 4 fhLevT)
    (hL : Levi.embSL 𝔽₃ 4 fhLevL * c = c * Levi.embSL 𝔽₃ 4 fhLevL) :
    β • statedPointFamily (coe_quadPlus 4 𝔽₃) = statedPointFamily (coe_quadPlus 4 𝔽₃) := by
  have hK : Nat.card 𝔽₃ = 3 :=
    CFSG.ClassicalInvolution.ModelFacts.TG3.natCard_galoisField_three
  obtain ⟨h3, -⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  have hconj : ∀ X : V₈ ≃ₗ[𝔽₃] V₈, X * c = c * X → (θ * X * θ⁻¹) * a = a * (θ * X * θ⁻¹) := by
    intro X hX
    rw [hac]
    calc θ * X * θ⁻¹ * (θ * c * θ⁻¹) = θ * (X * c) * θ⁻¹ := by group
      _ = θ * (c * X) * θ⁻¹ := by rw [hX]
      _ = θ * c * θ⁻¹ * (θ * X * θ⁻¹) := by group
  have hcube : ∀ A : SL(4, 𝔽₃), A ^ 3 = 1 →
      (θ * Levi.embSL 𝔽₃ 4 A * θ⁻¹) ^ 3 = 1 := by
    intro A hA
    rw [conj_pow, ← map_pow, hA, map_one, mul_one, mul_inv_cancel]
  refine fh_smul_of_cubes hodd hβ (u₁ := θ * Levi.embSL 𝔽₃ 4 fhLevT * θ⁻¹)
    (u₂ := θ * Levi.embSL 𝔽₃ 4 fhLevL * θ⁻¹) (u₃ := θ * Levi.embSL 𝔽₃ 4 fhLevT * θ⁻¹)
    (conj_mem_elementaryGroup hθ (fh_embSL_mem_elementary _))
    (conj_mem_elementaryGroup hθ (fh_embSL_mem_elementary _))
    (conj_mem_elementaryGroup hθ (fh_embSL_mem_elementary _))
    (hconj _ hT) (hconj _ hL) (hconj _ hT) (hcube _ (fhLevT_pow_three h3))
    (hcube _ (fhLevL_pow_three h3)) (hcube _ (fhLevT_pow_three h3)) ?_
  intro v
  have hy : θ * Levi.embSL 𝔽₃ 4 fhLevT * θ⁻¹ * (θ * Levi.embSL 𝔽₃ 4 fhLevL * θ⁻¹) *
      (θ * Levi.embSL 𝔽₃ 4 fhLevT * θ⁻¹) =
      θ * Levi.embSL 𝔽₃ 4 (fhLevT * fhLevL * fhLevT) * θ⁻¹ := by
    rw [map_mul, map_mul]
    group
  have hE2 := fh_embSL_sq (F := 𝔽₃) (A := fhLevT * fhLevL * fhLevT) fhLevW_sq
  rw [hy]
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, hE2,
    map_neg, LinearEquiv.apply_symm_apply]

end CFSG.OddStandard.SmallF3.Omega
