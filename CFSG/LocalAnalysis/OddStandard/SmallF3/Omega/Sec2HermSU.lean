module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermUni
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary Matrix
  CFSG.ComponentClassification.CatalogueBUnitaryIsometry CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary

@[expose] noncomputable def suToOrth : Su F9 3 1 4 →* OGroup (hermForm 4) :=
  (uidToOrth 4).comp (Subgroup.inclusion (SUid_le_Uid σ9 4))

theorem suToOrth_injective : Function.Injective suToOrth :=
  (uidToOrth_injective 4).comp (Subgroup.inclusion_injective _)

theorem suToOrth_comm_omega (s : Su F9 3 1 4) :
    suToOrth s * omegaOrth 4 = omegaOrth 4 * suToOrth s :=
  uidToOrth_comm_omega _

@[expose] noncomputable def omegaUnit : F9ˣ :=
  ⟨omega9, -omega9, by rw [mul_neg, omega9_mul_omega9, neg_neg],
    by rw [neg_mul, omega9_mul_omega9, neg_neg]⟩

theorem conjTr_scalar_four (c : F9) :
    conjTr σ9 (Matrix.scalar (Fin 4) c) = Matrix.scalar (Fin 4) (σ9 c) := by
  refine Matrix.ext fun i j => ?_
  simp [conjTr, Matrix.scalar_apply, Matrix.diagonal_apply, eq_comm]

theorem omega9_pow_four : omega9 ^ 4 = 1 := by
  have h2 : omega9 ^ 2 = -1 := by rw [pow_two, omega9_mul_omega9]
  calc omega9 ^ 4 = (omega9 ^ 2) ^ 2 := by ring
    _ = 1 := by rw [h2]; norm_num

theorem σ9_omega : σ9 omega9 = -omega9 := by
  apply QuadraticAlgebra.ext
  · rw [σ9_re]
    simp [omega9]
  · rw [σ9_im]
    simp [omega9]

theorem scalar_omega_mem : (Matrix.GeneralLinearGroup.scalar (Fin 4) omegaUnit : GL (Fin 4) F9) ∈
    SUid σ9 4 := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal]
    simpa [omegaUnit] using omega9_pow_four
  · rw [Matrix.GeneralLinearGroup.coe_scalar, conjTr_scalar_four, ← map_mul]
    show Matrix.scalar (Fin 4) (σ9 omega9 * omega9) = 1
    rw [σ9_omega, neg_mul, omega9_mul_omega9, neg_neg, map_one]

@[expose] noncomputable def hermOmegaSU : Su F9 3 1 4 :=
  ⟨Matrix.GeneralLinearGroup.scalar (Fin 4) omegaUnit, scalar_omega_mem⟩

theorem suMat_hermOmegaSU : suMat hermOmegaSU = Matrix.scalar (Fin 4) omega9 := rfl

theorem suToOrth_hermOmegaSU : suToOrth hermOmegaSU = omegaOrth 4 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change suMat hermOmegaSU *ᵥ x = omega9 • x
  rw [suMat_hermOmegaSU, Matrix.scalar_apply]
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

theorem hermOmegaSU_mem_center : hermOmegaSU ∈ Subgroup.center (Su F9 3 1 4) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_hermOmegaSU]
  exact (Matrix.scalar_commute _ (Commute.all _) _).symm.eq

@[expose] noncomputable def hermNegSU : Su F9 3 1 4 := hermOmegaSU * hermOmegaSU

theorem suToOrth_hermNegSU : suToOrth hermNegSU = piOrth (hermForm 4) := by
  rw [hermNegSU, map_mul, suToOrth_hermOmegaSU, omegaOrth_mul_self]

theorem hermNegSU_mul_self : hermNegSU * hermNegSU = 1 :=
  suToOrth_injective (by rw [map_mul, suToOrth_hermNegSU, piOrth_mul_self, map_one])

theorem neg_one_ne_one_F9 : (-1 : F9) ≠ 1 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  simp only [QuadraticAlgebra.re_neg, QuadraticAlgebra.re_one] at this
  exact absurd this (by decide)

theorem piOrth_ne_one_four : piOrth (hermForm 4) ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : OGroup (hermForm 4) =>
    (g : (Fin 4 → F9) ≃ₗ[ZMod 3] (Fin 4 → F9)) (Pi.single 0 1)) h
  have h2 := congrFun h1 0
  simp only [coe_piOrth_apply] at h2
  exact neg_one_ne_one_F9 (by simpa using h2)

theorem hermNegSU_ne_one : hermNegSU ≠ 1 := by
  intro h
  apply piOrth_ne_one_four
  rw [← suToOrth_hermNegSU, h, map_one]

theorem orderOf_hermNegSU : orderOf hermNegSU = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact hermNegSU_mul_self) hermNegSU_ne_one

theorem hermNegSU_mem_center : hermNegSU ∈ Subgroup.center (Su F9 3 1 4) :=
  Subgroup.mul_mem _ hermOmegaSU_mem_center hermOmegaSU_mem_center

theorem suMat_hermNegSU : suMat hermNegSU = Matrix.scalar (Fin 4) (-1 : F9) := by
  rw [hermNegSU, suMat_mul, suMat_hermOmegaSU, ← map_mul, omega9_mul_omega9]

theorem hermNegSU_not_mem_rootSU2 : hermNegSU ∉ rootSU2 F9 3 1 (by norm_num : 2 ≤ 4) := by
  rintro ⟨A, hA⟩
  have h1 := congrArg suMat hA
  rw [suMat_blockEmb, suMat_hermNegSU] at h1
  have h2 := congrFun (congrFun h1 3) 3
  simp [blockMat, blockSel_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
    Matrix.scalar_apply] at h2
  exact neg_one_ne_one_F9 h2.symm

end CFSG.OddStandard.SmallF3.Omega
