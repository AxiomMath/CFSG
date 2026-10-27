module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.AGLEmbedding.OmegaMinusPerf

open CFSG.LinearAlgebra Module CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.LieType.BorelTits

noncomputable def omegaBasis : Module.Basis (Fin 2) (ZMod 2) OmegaField :=
  (AdjoinRoot.powerBasis' omegaPoly_monic).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis'_dim, omegaPoly_natDegree]))

theorem omegaBasis_zero : omegaBasis 0 = 1 := by
  simp [omegaBasis, PowerBasis.coe_basis]

theorem omegaBasis_one : omegaBasis 1 = omega := by
  simp [omegaBasis, PowerBasis.coe_basis]

noncomputable def omegaRe : OmegaField →ₗ[ZMod 2] ZMod 2 := omegaBasis.coord 0

noncomputable def omegaIm : OmegaField →ₗ[ZMod 2] ZMod 2 := omegaBasis.coord 1

theorem mk_eq_smul (α β : ZMod 2) :
    algebraMap (ZMod 2) OmegaField α + algebraMap (ZMod 2) OmegaField β * omega =
      α • omegaBasis 0 + β • omegaBasis 1 := by
  rw [omegaBasis_zero, omegaBasis_one, Algebra.smul_def, Algebra.smul_def, mul_one]

theorem omegaRe_mk (α β : ZMod 2) :
    omegaRe (algebraMap (ZMod 2) OmegaField α + algebraMap (ZMod 2) OmegaField β * omega) = α := by
  rw [mk_eq_smul]
  simp [omegaRe, Module.Basis.coord_apply, Module.Basis.repr_self]

theorem omegaIm_mk (α β : ZMod 2) :
    omegaIm (algebraMap (ZMod 2) OmegaField α + algebraMap (ZMod 2) OmegaField β * omega) = β := by
  rw [mk_eq_smul]
  simp [omegaIm, Module.Basis.coord_apply, Module.Basis.repr_self]

theorem eq_re_im (z : OmegaField) :
    z = algebraMap (ZMod 2) OmegaField (omegaRe z) +
      algebraMap (ZMod 2) OmegaField (omegaIm z) * omega := by
  rw [mk_eq_smul]
  conv_lhs => rw [← omegaBasis.sum_repr z]
  rw [Fin.sum_univ_two]
  rfl

theorem zmod_two_cases' (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem omega_pow_three : omega ^ 3 = 1 := by
  have h := omega_sq
  have h2 := omegaField_two_eq_zero
  linear_combination (omega + 1) * h + omega * h2

theorem cube_mk (α β : ZMod 2) :
    (algebraMap (ZMod 2) OmegaField α + algebraMap (ZMod 2) OmegaField β * omega) ^ 3 =
      algebraMap (ZMod 2) OmegaField (α + β + α * β) := by
  have h := omega_sq
  have h3 := omega_pow_three
  have h2 := omegaField_two_eq_zero
  rcases zmod_two_cases' α with rfl | rfl <;> rcases zmod_two_cases' β with rfl | rfl
  · simp
  · simp [h3]
  · simp
  · have : (1 + 1 + 1 * 1 : ZMod 2) = 1 := by decide
    rw [this]
    simp only [map_one, one_mul]
    linear_combination (3 * omega + 2) * h2 + 3 * h + h3

theorem omega_mul_mk (α β : ZMod 2) :
    omega * (algebraMap (ZMod 2) OmegaField α + algebraMap (ZMod 2) OmegaField β * omega) =
      algebraMap (ZMod 2) OmegaField β + algebraMap (ZMod 2) OmegaField (α + β) * omega := by
  rw [map_add]
  linear_combination (algebraMap (ZMod 2) OmegaField β) * omega_sq

theorem omega_mul_eq (z : OmegaField) :
    omega * z = algebraMap (ZMod 2) OmegaField (omegaIm z) +
      algebraMap (ZMod 2) OmegaField (omegaRe z + omegaIm z) * omega := by
  have := omega_mul_mk (omegaRe z) (omegaIm z)
  rwa [← eq_re_im z] at this

theorem omegaRe_omega_mul (z : OmegaField) : omegaRe (omega * z) = omegaIm z := by
  rw [omega_mul_eq, omegaRe_mk]

theorem omegaIm_omega_mul (z : OmegaField) : omegaIm (omega * z) = omegaRe z + omegaIm z := by
  rw [omega_mul_eq, omegaIm_mk]

theorem natCard_omegaField' : Nat.card OmegaField = 4 := by
  have : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_omegaField, Nat.card_zmod]
  norm_num

local instance : Finite OmegaField :=
  have : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
  Module.finite_of_finite (ZMod 2)

local instance : CharP OmegaField 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) OmegaField).injective 2

noncomputable abbrev omegaSigma : OmegaField ≃+* OmegaField := unitaryInvolution OmegaField 2 1

theorem omegaSigma_apply (z : OmegaField) : omegaSigma z = z ^ 2 := by
  rw [unitaryInvolution_apply]
  simp

theorem isUnitaryInvolution_omegaSigma : IsUnitaryInvolution omegaSigma :=
  isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) (by rw [natCard_omegaField']; norm_num)

theorem isPerfect_SUid_omega {k : ℕ} (hk : 4 ≤ k) : Group.IsPerfect (SUid omegaSigma k) :=
  isPerfect_SUid isUnitaryInvolution_omegaSigma (by omega) fun h => by omega

open Matrix in
theorem sum_cube_mulVec {k : ℕ} {B : GL (Fin k) OmegaField} (hB : B ∈ SUid omegaSigma k)
    (z : Fin k → OmegaField) :
    ∑ i, ((B : Matrix (Fin k) (Fin k) OmegaField) *ᵥ z) i ^ 3 = ∑ i, z i ^ 3 := by
  have hcube : ∀ t : OmegaField, t ^ 3 = omegaSigma t * t := fun t => by
    rw [omegaSigma_apply]; ring
  simp only [hcube]
  have h1 : (fun i => omegaSigma (((B : Matrix (Fin k) (Fin k) OmegaField) *ᵥ z) i)) =
      (((B : Matrix (Fin k) (Fin k) OmegaField).map omegaSigma) *ᵥ (omegaSigma ∘ z)) := by
    funext i
    exact RingHom.map_mulVec omegaSigma.toRingHom _ _ i
  have h2 : ∑ i, omegaSigma (((B : Matrix (Fin k) (Fin k) OmegaField) *ᵥ z) i) *
      ((B : Matrix (Fin k) (Fin k) OmegaField) *ᵥ z) i =
      (fun i => omegaSigma (((B : Matrix (Fin k) (Fin k) OmegaField) *ᵥ z) i)) ⬝ᵥ
        ((B : Matrix (Fin k) (Fin k) OmegaField) *ᵥ z) := rfl
  rw [h2, h1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have hB2 : conjTr omegaSigma (B : Matrix (Fin k) (Fin k) OmegaField) *
      (B : Matrix (Fin k) (Fin k) OmegaField) = 1 := hB.2
  rw [conjTr] at hB2
  rw [hB2, Matrix.one_mulVec]
  rfl

end CFSG.AGLEmbedding.OmegaMinusPerf
