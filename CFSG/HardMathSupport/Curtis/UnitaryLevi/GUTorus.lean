module

public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryDet

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary

@[expose] noncomputable def blockScalarEnd {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] (x : Module.End K V) (a : K[X]) (μ : K) : Module.End K V :=
  1 + (μ - 1) • primaryProjection x a

section Basic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {x : Module.End K V} {a : K[X]}

omit [FiniteDimensional K V] in
theorem blockScalarEnd_apply (μ : K) (v : V) :
    blockScalarEnd x a μ v = v + (μ - 1) • primaryProjection x a v := rfl

theorem blockScalarEnd_of_mem (hsq : Squarefree (minpoly K x)) (ha : a ∈ primaryFactors x)
    (μ : K) {v : V} (hv : v ∈ primaryComponent x a) : blockScalarEnd x a μ v = μ • v := by
  rw [blockScalarEnd_apply, primaryProjection_of_mem hsq ha hv, sub_smul, one_smul]
  abel

theorem blockScalarEnd_of_mem_ne (hsq : Squarefree (minpoly K x)) (ha : a ∈ primaryFactors x)
    {b : K[X]} (hb : b ∈ primaryFactors x) (hba : b ≠ a) (μ : K) {v : V}
    (hv : v ∈ primaryComponent x b) : blockScalarEnd x a μ v = v := by
  rw [blockScalarEnd_apply, primaryProjection_of_mem_ne hsq ha hb hba hv, smul_zero, add_zero]

theorem blockScalarEnd_mul (hsq : Squarefree (minpoly K x)) (ha : a ∈ primaryFactors x)
    (μ μ' : K) :
    blockScalarEnd x a μ * blockScalarEnd x a μ' = blockScalarEnd x a (μ * μ') := by
  ext v
  have h1 : primaryProjection x a (primaryProjection x a v) = primaryProjection x a v :=
    primaryProjection_of_mem hsq ha (primaryProjection_mem hsq ha v)
  simp only [Module.End.mul_apply, blockScalarEnd_apply, map_add, map_smul, h1]
  module

omit [FiniteDimensional K V] in
theorem blockScalarEnd_one : blockScalarEnd x a 1 = 1 := by
  ext v
  simp [blockScalarEnd_apply]

omit [FiniteDimensional K V] in
theorem commute_blockScalarEnd (μ : K) : Commute (blockScalarEnd x a μ) x := by
  refine (Commute.one_left x).add_left ((Commute.smul_left ?_ (μ - 1)))
  exact (commute_aeval (Commute.refl x) _).symm

@[expose] noncomputable def blockScalarGL (hsq : Squarefree (minpoly K x))
    (ha : a ∈ primaryFactors x) {μ : K} (hμ : μ ≠ 0) : LinearMap.GeneralLinearGroup K V :=
  ⟨blockScalarEnd x a μ, blockScalarEnd x a μ⁻¹,
    by rw [blockScalarEnd_mul hsq ha, mul_inv_cancel₀ hμ, blockScalarEnd_one],
    by rw [blockScalarEnd_mul hsq ha, inv_mul_cancel₀ hμ, blockScalarEnd_one]⟩

@[simp] theorem coe_blockScalarGL (hsq : Squarefree (minpoly K x)) (ha : a ∈ primaryFactors x)
    {μ : K} (hμ : μ ≠ 0) :
    ((blockScalarGL hsq ha hμ : LinearMap.GeneralLinearGroup K V) : Module.End K V) =
      blockScalarEnd x a μ := rfl

end Basic

section Unitary

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
  (H : UnitaryPrimaryData σ B x)
  {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V)) (hself : dualPoly σ a = a)
include H ha hself

theorem blockScalarEnd_isometry {μ : K} (hμ : σ μ * μ = 1) (v w : V) :
    B (blockScalarEnd (x : Module.End K V) a μ v) (blockScalarEnd (x : Module.End K V) a μ w) =
      B v w := by
  have hadj : H.adj (primaryProjection (x : Module.End K V) a) =
      primaryProjection (x : Module.End K V) a := by
    rw [adj_primaryProjection H ha, hself]
  have hs : ∀ v w, B (primaryProjection (x : Module.End K V) a v) w =
      B v (primaryProjection (x : Module.End K V) a w) := fun v w => by
    rw [H.adj_spec, hadj]
  have h1 : primaryProjection (x : Module.End K V) a (primaryProjection (x : Module.End K V) a w)
      = primaryProjection (x : Module.End K V) a w :=
    primaryProjection_of_mem H.squarefree ha (primaryProjection_mem H.squarefree ha w)
  simp only [blockScalarEnd_apply, map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, hs, h1]
  rw [map_sub, map_one]
  simp only [RingHom.id_apply]
  linear_combination (B v (primaryProjection (x : Module.End K V) a w)) * hμ

omit hself in
theorem det_blockScalarEnd (μ : K) :
    LinearMap.det (blockScalarEnd (x : Module.End K V) a μ) =
      μ ^ Module.finrank K (primaryComponent (x : Module.End K V) a) := by
  have hcomm := commute_blockScalarEnd (x := (x : Module.End K V)) (a := a) μ
  rw [det_eq_det_restrict_of_trivial_off H.squarefree ha hcomm
    (fun b hb hba v hv => blockScalarEnd_of_mem_ne H.squarefree ha hb hba μ hv)]
  have : (blockScalarEnd (x : Module.End K V) a μ).restrict
      (fun _ hv => apply_mem_primaryComponent hcomm hv :
        ∀ v ∈ primaryComponent (x : Module.End K V) a,
          blockScalarEnd (x : Module.End K V) a μ v ∈
            primaryComponent (x : Module.End K V) a) = μ • LinearMap.id := by
    ext v
    exact congrArg Subtype.val (Subtype.ext (blockScalarEnd_of_mem H.squarefree ha μ v.2))
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]

end Unitary

section Special

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
  (H : UnitaryPrimaryData σ B x)
include H

theorem exists_special_unitary_block_scalar {a b : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) (hb : b ∈ primaryFactors (x : Module.End K V))
    (hsa : dualPoly σ a = a) (hsb : dualPoly σ b = b) (hab : a ≠ b)
    (hna : Module.finrank K (primaryComponent (x : Module.End K V) a) = 1)
    (hnb : Module.finrank K (primaryComponent (x : Module.End K V) b) = 1)
    {ν : K} (hν : σ ν * ν = 1) :
    ∃ g : LinearMap.GeneralLinearGroup K V, g ∈ sesqSpecialUnitaryGroup B ∧
      Commute (g : Module.End K V) (x : Module.End K V) ∧
      (∀ v ∈ primaryComponent (x : Module.End K V) a, (g : Module.End K V) v = ν • v) ∧
      (∀ v ∈ primaryComponent (x : Module.End K V) b, (g : Module.End K V) v = ν⁻¹ • v) := by
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp at hν
  have hν' : σ ν⁻¹ * ν⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hν, inv_one]
  have hsq := H.squarefree
  set ga := blockScalarGL hsq ha hν0 with hga
  set gb := blockScalarGL hsq hb (inv_ne_zero hν0) with hgb
  refine ⟨ga * gb, ?_, ?_, ?_, ?_⟩
  · rw [mem_sesqSpecialUnitaryGroup]
    refine ⟨Subgroup.mul_mem _ ?_ ?_, ?_⟩
    · exact fun v w => blockScalarEnd_isometry H ha hsa hν v w
    · exact fun v w => blockScalarEnd_isometry H hb hsb hν' v w
    · rw [Units.val_mul, map_mul]
      change LinearMap.det (blockScalarEnd (x : Module.End K V) a ν) *
        LinearMap.det (blockScalarEnd (x : Module.End K V) b ν⁻¹) = 1
      rw [det_blockScalarEnd H ha ν, det_blockScalarEnd H hb ν⁻¹, hna, hnb, pow_one, pow_one,
        mul_inv_cancel₀ hν0]
  · rw [Units.val_mul]
    exact (commute_blockScalarEnd ν).mul_left (commute_blockScalarEnd ν⁻¹)
  · intro v hv
    rw [Units.val_mul, Module.End.mul_apply]
    change blockScalarEnd (x : Module.End K V) a ν (blockScalarEnd (x : Module.End K V) b ν⁻¹ v) = _
    rw [blockScalarEnd_of_mem_ne hsq hb ha hab ν⁻¹ hv, blockScalarEnd_of_mem hsq ha ν hv]
  · intro v hv
    rw [Units.val_mul, Module.End.mul_apply]
    change blockScalarEnd (x : Module.End K V) a ν (blockScalarEnd (x : Module.End K V) b ν⁻¹ v) = _
    rw [blockScalarEnd_of_mem hsq hb ν⁻¹ hv, map_smul,
      blockScalarEnd_of_mem_ne hsq ha hb (Ne.symm hab) ν hv]

end Special

end CFSG.HardMathSupport.Curtis.UnitaryLevi
