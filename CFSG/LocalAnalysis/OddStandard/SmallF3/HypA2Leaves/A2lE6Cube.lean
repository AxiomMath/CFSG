module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lE6Torus
public import CFSG.LieType.Chevalley.E6A5CubeLevi

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.E6A5Cube
  CFSG.LieType.Chevalley.ExteriorCube exteriorPower Set Matrix
  CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Universal.Unitary (SU conjTr)

variable {K : Type} [Field K]

theorem a2lE6_neg_one_pow_six : (-1 : K) ^ 6 = 1 := by
  norm_num

theorem a2lE6_coe_scalar_neg_one :
    ((Matrix.GeneralLinearGroup.scalar (Fin 6) (-1 : Kˣ) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = (-1 : K) • (1 : Matrix (Fin 6) (Fin 6) K) := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rfl

theorem a2lE6_scalar_neg_one_mem_SU (σ : K ≃+* K) :
    Matrix.GeneralLinearGroup.scalar (Fin 6) (-1 : Kˣ) ∈ SU σ 6 := by
  refine ⟨?_, ?_⟩
  · rw [a2lE6_coe_scalar_neg_one, Matrix.det_smul, det_one, mul_one, Fintype.card_fin]
    exact a2lE6_neg_one_pow_six
  · have h : conjTr σ ((-1 : K) • (1 : Matrix (Fin 6) (Fin 6) K)) =
        (-1 : K) • (1 : Matrix (Fin 6) (Fin 6) K) := by
      ext i j
      by_cases hij : i = j
      · simp [conjTr, Matrix.smul_apply, Matrix.one_apply, hij]
      · have hji : ¬ j = i := fun h => hij h.symm
        simp [conjTr, Matrix.smul_apply, Matrix.one_apply, hij, hji]
    rw [a2lE6_coe_scalar_neg_one, h, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul]
    simp

theorem a2lE6_conjSU_neg_one (σ : K ≃+* K) {ζ : K} (hζ : ζ ≠ 0) (x : SU σ 6)
    (hx : (x : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) (-1 : Kˣ)) :
    conjSU σ hζ x = scalarSL K (-1) a2lE6_neg_one_pow_six := by
  apply Subtype.ext
  change diagonal (eDiag K ζ) * ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      diagonal (fun i => (eDiag K ζ i)⁻¹) = (-1 : K) • (1 : Matrix (Fin 6) (Fin 6) K)
  rw [hx, a2lE6_coe_scalar_neg_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    diag_mul_inv _ (eDiag_ne_zero hζ)]

section Cube


theorem a2lE6_psiA_da :
    psiA K ⟨rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5), a2lE6_da_mem_groupA⟩ =
      cubeHom (scalarSL K (-1) a2lE6_neg_one_pow_six) := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  have hL : (psiA K ⟨rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5), a2lE6_da_mem_groupA⟩ :
      Module.End K (⋀[K]^3 (Fin 6 → K))) x = (-1 : K) • x := by
    rw [psiA_apply]
    have : restrictEndA K ⟨rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5), a2lE6_da_mem_groupA⟩
        ((phiA K).symm x) = (-1 : K) • (phiA K).symm x :=
      Subtype.ext (by
        rw [restrictEndA_apply, Submodule.coe_smul, neg_one_smul]
        exact a2lE6_da_apply_moduleA ((phiA K).symm x).2)
    rw [this, map_smul, LinearEquiv.apply_symm_apply]
  have hR : (cubeHom (scalarSL K (-1) a2lE6_neg_one_pow_six) :
      Module.End K (⋀[K]^3 (Fin 6 → K))) x = (-1 : K) • x := by
    rw [coe_cubeHom]
    change cubeEnd ((-1 : K) • (1 : Matrix (Fin 6) (Fin 6) K)) x = (-1 : K) • x
    rw [cubeEnd_smul_one, LinearMap.smul_apply, Module.End.one_apply,
      show ((-1 : K) ^ 3) = -1 by norm_num]
  exact hL.trans hR.symm

variable [Finite K]

theorem a2lE6_liftA_neg_one :
    liftA K (scalarSL K (-1) a2lE6_neg_one_pow_six) =
      ⟨rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5), a2lE6_da_mem_groupA⟩ :=
  liftA_eq_of_psiA_eq a2lE6_psiA_da

theorem a2lE6_leviHomA_neg_one (σ : K ≃+* K) {ζ : K} (hζ : ζ ≠ 0) (x : SU σ 6)
    (hx : (x : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) (-1 : Kˣ)) :
    ((leviHomA σ hζ x : groupA K) : ModGL Tag.E6 K) =
      rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5) := by
  rw [leviHomA, MonoidHom.comp_apply, a2lE6_conjSU_neg_one σ hζ x hx, a2lE6_liftA_neg_one]

end Cube

end CFSG.OddStandard.SmallF3.HypA2Leaves
