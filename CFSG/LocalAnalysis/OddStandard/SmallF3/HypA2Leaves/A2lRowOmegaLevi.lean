module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverL4

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] noncomputable def a2lLevi : GL (Fin 4) K →* GL (Fin 4 ⊕ Fin 4) K where
  toFun A :=
    ⟨fromBlocks (A : Matrix (Fin 4) (Fin 4) K) 0 0
        ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ,
      fromBlocks ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0
        (A : Matrix (Fin 4) (Fin 4) K)ᵀ,
      by rw [fromBlocks_multiply]; simp [← Matrix.transpose_mul],
      by rw [fromBlocks_multiply]; simp [← Matrix.transpose_mul]⟩
  map_one' := by
    ext1
    simp [fromBlocks_one]
  map_mul' A B := by
    ext1
    simp [fromBlocks_multiply, Matrix.transpose_mul, _root_.mul_inv_rev]

theorem a2lLevi_coe (A : GL (Fin 4) K) :
    ((a2lLevi A : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      fromBlocks (A : Matrix (Fin 4) (Fin 4) K) 0 0
        ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ :=
  rfl

@[expose] noncomputable def a2lLeviLin :
    GL (Fin 4) K →* ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
  (toLinEquiv (Fin 4 ⊕ Fin 4) K).toMonoidHom.comp a2lLevi

theorem a2lLeviLin_apply (A : GL (Fin 4) K) (v : Fin 4 ⊕ Fin 4 → K) :
    a2lLeviLin A v = Sum.elim ((A : Matrix (Fin 4) (Fin 4) K) *ᵥ (v ∘ Sum.inl))
      (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *ᵥ (v ∘ Sum.inr)) := by
  rw [a2lLeviLin, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, toLinEquiv_apply, a2lLevi_coe,
    fromBlocks_mulVec]
  simp

theorem a2lLeviLin_mem_orthogonalGroup (A : GL (Fin 4) K) :
    a2lLeviLin A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  rw [quadPlus_apply, quadPlus_apply]
  simp only [a2lLeviLin_apply, Sum.elim_inl, Sum.elim_inr]
  have key : ((A : Matrix (Fin 4) (Fin 4) K) *ᵥ (v ∘ Sum.inl)) ⬝ᵥ
      (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *ᵥ (v ∘ Sum.inr)) =
        (v ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr) := by
    rw [dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, Units.inv_mul,
      Matrix.one_mulVec]
  exact key

theorem a2lLeviLin_injective : Function.Injective (a2lLeviLin (K := K)) := by
  intro A B h
  refine Units.ext (Matrix.ext_of_mulVec_single fun i => ?_)
  have h1 := congrArg (fun g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) =>
    fun j => g (Sum.elim (Pi.single i 1) 0) (Sum.inl j)) h
  simp only [a2lLeviLin_apply, Sum.elim_inl, Sum.elim_comp_inl] at h1
  exact h1

theorem a2lLeviLin_of_eq_neg_one {A : GL (Fin 4) K} (hA : (A : Matrix (Fin 4) (Fin 4) K) = -1) :
    a2lLeviLin A = LinearEquiv.neg K := by
  have hinv : ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = -1 := by
    have h := Units.mul_inv A
    rw [hA, neg_one_mul] at h
    exact neg_eq_iff_eq_neg.mp h
  refine LinearEquiv.ext fun v => ?_
  rw [a2lLeviLin_apply, hA, hinv]
  ext (i | i) <;> simp [Matrix.neg_mulVec]

@[expose] noncomputable def a2lNineLevi [Fintype K] (hF : Fintype.card K = 3) :
    SL(2, GaloisField 3 2) →* ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
  a2lLeviLin.comp (SpecialLinearGroup.toGL.comp (a2lNineSL4 hF))

theorem a2lNineLevi_injective [Fintype K] (hF : Fintype.card K = 3) :
    Function.Injective (a2lNineLevi hF) :=
  a2lLeviLin_injective.comp
    (SpecialLinearGroup.toGL_injective.comp (a2lNineSL4_injective hF))

theorem a2lNineLevi_mem_orthogonalGroup [Fintype K] (hF : Fintype.card K = 3)
    (g : SL(2, GaloisField 3 2)) :
    a2lNineLevi hF g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
  a2lLeviLin_mem_orthogonalGroup _

theorem a2lNineLevi_negOne [Fintype K] (hF : Fintype.card K = 3) :
    a2lNineLevi hF (a2lNegOne (GaloisField 3 2)) = LinearEquiv.neg K :=
  a2lLeviLin_of_eq_neg_one (a2lNineSL4_negOne hF)

end CFSG.OddStandard.SmallF3.HypA2Leaves
