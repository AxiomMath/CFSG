module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Reduced

public section

namespace CFSG.LinearAlgebra

open Polynomial

@[expose] noncomputable def omegaPoly : (ZMod 2)[X] := X ^ 2 + X + 1

theorem omegaPoly_natDegree : omegaPoly.natDegree = 2 := by
  unfold omegaPoly
  compute_degree!

theorem omegaPoly_monic : omegaPoly.Monic := by
  unfold omegaPoly
  monicity!

theorem omegaPoly_irreducible : Irreducible omegaPoly := by
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [omegaPoly_natDegree]; decide) ?_
  intro x
  simp only [omegaPoly, IsRoot.def, eval_add, eval_pow, eval_X, eval_one]
  revert x
  decide

instance : Fact (Irreducible omegaPoly) :=
  ⟨omegaPoly_irreducible⟩

abbrev OmegaField : Type :=
  AdjoinRoot omegaPoly

noncomputable abbrev omega : OmegaField :=
  AdjoinRoot.root omegaPoly

theorem omegaField_two_eq_zero : (2 : OmegaField) = 0 := by
  have h : (2 : OmegaField) = algebraMap (ZMod 2) OmegaField 2 := by
    rw [map_ofNat]
  rw [h, show (2 : ZMod 2) = 0 from rfl, map_zero]

theorem omega_sq : omega ^ 2 = omega + 1 := by
  have h : AdjoinRoot.mk omegaPoly (X ^ 2 + X + 1) = 0 := AdjoinRoot.mk_self
  rw [map_add, map_add, map_pow, AdjoinRoot.mk_X, map_one] at h
  have h2 : (omega + 1) + (omega + 1) = 0 := by
    rw [← two_mul, omegaField_two_eq_zero, zero_mul]
  calc omega ^ 2 = omega ^ 2 + omega + 1 + (omega + 1) := by
        rw [add_assoc (omega ^ 2), add_assoc, h2, add_zero]
    _ = omega + 1 := by rw [h, zero_add]

theorem omegaField_eq (x : OmegaField) :
    ∃ a b : ZMod 2, x = algebraMap (ZMod 2) OmegaField a + algebraMap (ZMod 2) OmegaField b * omega
    := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  have hdeg : (p %ₘ omegaPoly).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt p omegaPoly_monic (by
      intro h
      have := congrArg natDegree h
      rw [omegaPoly_natDegree, natDegree_one] at this
      exact absurd this (by decide))
    rw [omegaPoly_natDegree] at this
    omega
  have hrep : AdjoinRoot.mk omegaPoly (p %ₘ omegaPoly) = AdjoinRoot.mk omegaPoly p := by
    rw [← AdjoinRoot.modByMonicHom_mk omegaPoly_monic]
    exact AdjoinRoot.mk_leftInverse omegaPoly_monic _
  have hqe := eq_X_add_C_of_natDegree_le_one hdeg
  refine ⟨(p %ₘ omegaPoly).coeff 0, (p %ₘ omegaPoly).coeff 1, ?_⟩
  rw [← hrep]
  conv_lhs => rw [hqe]
  rw [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.mk_C, add_comm,
    AdjoinRoot.algebraMap_eq]

theorem finrank_omegaField : Module.finrank (ZMod 2) OmegaField = 2 := by
  rw [(AdjoinRoot.powerBasis' omegaPoly_monic).finrank, AdjoinRoot.powerBasis'_dim,
    omegaPoly_natDegree]

theorem exists_omegaField_frobenius : ∃ σ : OmegaField ≃+* OmegaField, ∀ x, σ x = x ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP OmegaField 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) OmegaField).injective 2
  have : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
  have : Finite OmegaField := Module.finite_of_finite (ZMod 2)
  refine ⟨RingEquiv.ofBijective (frobenius OmegaField 2)
    (Finite.injective_iff_bijective.1 (frobenius_inj OmegaField 2)), fun x => ?_⟩
  rfl

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem sq_add_self_add_one_eq_zero {z : Module.End (ZMod 2) V} (hz3 : z ^ 3 = 1)
    (hfix : ∀ v, z v = v → v = 0) : z ^ 2 + z + 1 = 0 := by
  ext v
  apply hfix
  have h3 : z (z (z v)) = v := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_two, ← pow_succ, hz3,
      Module.End.one_apply]
  simp only [LinearMap.add_apply, Module.End.one_apply, pow_two, Module.End.mul_apply, map_add,
    h3]
  abel

theorem fpf_relation {z : LinearMap.GeneralLinearGroup (ZMod 2) V} (hz : orderOf z = 3)
    (hfix : ∀ v, (z : V →ₗ[ZMod 2] V) v = v → v = 0) :
    (z : Module.End (ZMod 2) V) ^ 2 + z + 1 = 0 := by
  refine sq_add_self_add_one_eq_zero ?_ hfix
  rw [← Units.val_pow_eq_pow_val, ← hz, pow_orderOf_eq_one, Units.val_one]

@[expose] noncomputable def omegaHom (z : Module.End (ZMod 2) V) (hz : z ^ 2 + z + 1 = 0) :
    OmegaField →+* Module.End (ZMod 2) V :=
  Ideal.Quotient.lift _ (aeval z).toRingHom fun p hp => by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hp
    simp [omegaPoly, hz]

theorem omegaHom_mk (z : Module.End (ZMod 2) V) (hz : z ^ 2 + z + 1 = 0) (p : (ZMod 2)[X]) :
    omegaHom z hz (AdjoinRoot.mk omegaPoly p) = aeval z p :=
  rfl

theorem omegaHom_omega (z : Module.End (ZMod 2) V) (hz : z ^ 2 + z + 1 = 0) :
    omegaHom z hz omega = z := by
  change omegaHom z hz (AdjoinRoot.mk omegaPoly X) = z
  rw [omegaHom_mk, aeval_X]

theorem omegaHom_algebraMap (z : Module.End (ZMod 2) V) (hz : z ^ 2 + z + 1 = 0) (c : ZMod 2) :
    omegaHom z hz (algebraMap (ZMod 2) OmegaField c) = algebraMap (ZMod 2) _ c := by
  rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, omegaHom_mk, aeval_C]

@[expose, instance_reducible] noncomputable def omegaModule
    (z : LinearMap.GeneralLinearGroup (ZMod 2) V) (hz : orderOf z = 3)
    (hfix : ∀ v, (z : V →ₗ[ZMod 2] V) v = v → v = 0) : Module OmegaField V :=
  Module.compHom V (omegaHom (z : Module.End (ZMod 2) V) (fpf_relation hz hfix))

section Module

variable (z : LinearMap.GeneralLinearGroup (ZMod 2) V) (hz : orderOf z = 3)
  (hfix : ∀ v, (z : V →ₗ[ZMod 2] V) v = v → v = 0)

theorem omegaModule_smul (x : OmegaField) (v : V) :
    (letI := omegaModule z hz hfix; x • v) =
      omegaHom (z : Module.End (ZMod 2) V) (fpf_relation hz hfix) x v :=
  rfl

theorem omegaModule_smul_eq (a b : ZMod 2) (v : V) :
    (letI := omegaModule z hz hfix;
      (algebraMap (ZMod 2) OmegaField a + algebraMap (ZMod 2) OmegaField b * omega) • v) =
      a • v + b • (z : V →ₗ[ZMod 2] V) v := by
  rw [omegaModule_smul, map_add, map_mul, omegaHom_algebraMap, omegaHom_algebraMap,
    omegaHom_omega, LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
    Module.algebraMap_end_apply]

theorem omegaModule_omega_smul (v : V) :
    (letI := omegaModule z hz hfix; omega • v) = (z : V →ₗ[ZMod 2] V) v := by
  rw [omegaModule_smul, omegaHom_omega]

theorem omegaModule_algebraMap_smul (c : ZMod 2) (v : V) :
    (letI := omegaModule z hz hfix; algebraMap (ZMod 2) OmegaField c • v) = c • v := by
  rw [omegaModule_smul, omegaHom_algebraMap, Module.algebraMap_end_apply]

theorem omegaModule_isScalarTower :
    letI := omegaModule z hz hfix
    IsScalarTower (ZMod 2) OmegaField V := by
  let _i := omegaModule z hz hfix
  refine ⟨fun c x v => ?_⟩
  rw [Algebra.smul_def, mul_smul, omegaModule_algebraMap_smul z hz hfix]

theorem omegaField_sq (a b : ZMod 2) :
    (algebraMap (ZMod 2) OmegaField a + algebraMap (ZMod 2) OmegaField b * omega) ^ 2 =
      algebraMap (ZMod 2) OmegaField a + algebraMap (ZMod 2) OmegaField b * omega ^ 2 := by
  have ha : a ^ 2 = a := by revert a; decide
  have hb : b ^ 2 = b := by revert b; decide
  rw [add_sq, mul_pow, ← map_pow, ← map_pow, ha, hb, mul_assoc 2, omegaField_two_eq_zero,
    zero_mul, add_zero]

end Module

section Structure

variable [Module OmegaField V] [IsScalarTower (ZMod 2) OmegaField V]

omit [IsScalarTower (ZMod 2) OmegaField V] in
theorem smul_eq_of_omega_smul {z : V →ₗ[ZMod 2] V}
    (hc : ∀ (c : ZMod 2) (v : V), algebraMap (ZMod 2) OmegaField c • v = c • v)
    (hω : ∀ v, omega • v = z v) (a b : ZMod 2) (v : V) :
    (algebraMap (ZMod 2) OmegaField a + algebraMap (ZMod 2) OmegaField b * omega) • v =
      a • v + b • z v := by
  rw [add_smul, mul_smul, hω, hc, hc]

theorem sq_smul_eq_of_omega_smul {z : V →ₗ[ZMod 2] V} (hω : ∀ v, omega • v = z v)
    (a b : ZMod 2) (v : V) :
    (algebraMap (ZMod 2) OmegaField a + algebraMap (ZMod 2) OmegaField b * omega) ^ 2 • v =
      a • v + b • z (z v) := by
  rw [omegaField_sq, add_smul, mul_smul, pow_two, mul_smul, hω, hω, algebraMap_smul,
    algebraMap_smul]

theorem omega_eq_algebraMap :
    omega = algebraMap (ZMod 2) OmegaField 0 + algebraMap (ZMod 2) OmegaField 1 * omega := by
  rw [map_zero, map_one, zero_add, one_mul]

omit [Module OmegaField V] [IsScalarTower (ZMod 2) OmegaField V] in
theorem commute_iff_apply {g z : LinearMap.GeneralLinearGroup (ZMod 2) V} :
    g * z = z * g ↔ ∀ v, (g : V →ₗ[ZMod 2] V) ((z : V →ₗ[ZMod 2] V) v) =
      (z : V →ₗ[ZMod 2] V) ((g : V →ₗ[ZMod 2] V) v) := by
  rw [Units.ext_iff, Units.val_mul, Units.val_mul, LinearMap.ext_iff]
  rfl

theorem commute_iff_omega_linear {z : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hω : ∀ v, omega • v = (z : V →ₗ[ZMod 2] V) v) (g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
    g * z = z * g ↔ ∀ (x : OmegaField) (v : V),
      (g : V →ₗ[ZMod 2] V) (x • v) = x • (g : V →ₗ[ZMod 2] V) v := by
  rw [commute_iff_apply]
  constructor
  · intro h x v
    obtain ⟨a, b, rfl⟩ := omegaField_eq x
    rw [smul_eq_of_omega_smul (fun c v => algebraMap_smul OmegaField c v) hω,
      smul_eq_of_omega_smul (fun c v => algebraMap_smul OmegaField c v) hω, map_add, map_smul,
      map_smul, h]
  · intro h v
    rw [← hω, h, hω]

theorem conj_eq_sq_iff_semilinear {z : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hω : ∀ v, omega • v = (z : V →ₗ[ZMod 2] V) v) (g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
    g * z * g⁻¹ = z ^ 2 ↔ ∀ (x : OmegaField) (v : V),
      (g : V →ₗ[ZMod 2] V) (x • v) = x ^ 2 • (g : V →ₗ[ZMod 2] V) v := by
  rw [mul_inv_eq_iff_eq_mul, Units.ext_iff, Units.val_mul, Units.val_mul, LinearMap.ext_iff]
  change (∀ v, (g : V →ₗ[ZMod 2] V) ((z : V →ₗ[ZMod 2] V) v) =
    ((z ^ 2 : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
      ((g : V →ₗ[ZMod 2] V) v)) ↔ _
  have hz2 : ∀ w, ((z ^ 2 : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w =
      (z : V →ₗ[ZMod 2] V) ((z : V →ₗ[ZMod 2] V) w) := fun w => by
    rw [pow_two]
    rfl
  simp only [hz2]
  constructor
  · intro h x v
    obtain ⟨a, b, rfl⟩ := omegaField_eq x
    rw [smul_eq_of_omega_smul (fun c v => algebraMap_smul OmegaField c v) hω,
      sq_smul_eq_of_omega_smul hω, map_add, map_smul, map_smul, h]
  · intro h v
    rw [← hω, h, omega_eq_algebraMap, sq_smul_eq_of_omega_smul hω, zero_smul, one_smul,
      zero_add]

theorem mem_normalizer_zpowers_of_conj {G : Type*} [Group G] {z g : G} (hz3 : z ^ 3 = 1)
    (h : g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z ^ 2) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  have hzp : Subgroup.zpowers (MulAut.conj g z) = Subgroup.zpowers z := by
    rw [MulAut.conj_apply]
    rcases h with h | h
    · rw [h]
    · rw [h]
      refine le_antisymm (Subgroup.zpowers_le.2 (pow_mem (Subgroup.mem_zpowers z) 2))
        (Subgroup.zpowers_le.2 ?_)
      have : z = (z ^ 2) ^ 2 := by
        rw [← pow_mul, show (2 : ℕ) * 2 = 3 + 1 from rfl, pow_succ, hz3, one_mul]
      have h2 : (z ^ 2) ^ 2 ∈ Subgroup.zpowers (z ^ 2) := pow_mem (Subgroup.mem_zpowers _) 2
      rwa [← this] at h2
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  rw [← Subgroup.mem_map_iff_mem hinj, MonoidHom.map_zpowers]
  change MulAut.conj g x ∈ Subgroup.zpowers (MulAut.conj g z) ↔ _
  rw [hzp, MulAut.conj_apply]

theorem conj_eq_or_eq_sq_of_mem_normalizer {G : Type*} [Group G] {z g : G} (hz : orderOf z = 3)
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G)) :
    g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z ^ 2 := by
  have hmem := (Subgroup.mem_normalizer_iff.1 hg z).1 (Subgroup.mem_zpowers z)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hord : orderOf (g * z * g⁻¹) = 3 := by
    rw [← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
      orderOf_injective _ (MulAut.conj g).injective, hz]
  rw [← zpow_mod_orderOf, hz] at hk
  have h0 : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h3 : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  obtain ⟨r, hr⟩ : ∃ r, r = k % ((3 : ℕ) : ℤ) := ⟨_, rfl⟩
  rw [← hr] at hk h0 h3
  interval_cases r
  · rw [zpow_zero] at hk
    rw [← hk, orderOf_one] at hord
    exact absurd hord (by norm_num)
  · rw [zpow_one] at hk
    exact Or.inl hk.symm
  · refine Or.inr ?_
    rw [← hk]
    norm_cast

theorem omega_semilinear_structure [FiniteDimensional (ZMod 2) V]
    (z : LinearMap.GeneralLinearGroup (ZMod 2) V) (hz : orderOf z = 3)
    (hω : ∀ v, omega • v = (z : V →ₗ[ZMod 2] V) v) :
    Module.finrank (ZMod 2) V = 2 * Module.finrank OmegaField V ∧
    (∀ g : LinearMap.GeneralLinearGroup (ZMod 2) V, g * z = z * g ↔
      ∀ (x : OmegaField) (v : V), (g : V →ₗ[ZMod 2] V) (x • v) = x • (g : V →ₗ[ZMod 2] V) v) ∧
    (∀ e : V ≃ₗ[OmegaField] V, ∃ g : LinearMap.GeneralLinearGroup (ZMod 2) V,
      (∀ v, (g : V →ₗ[ZMod 2] V) v = e v) ∧ g * z = z * g) ∧
    (∀ g : LinearMap.GeneralLinearGroup (ZMod 2) V,
      g ∈ Subgroup.normalizer
          (Subgroup.zpowers z : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) ↔
        (∀ (x : OmegaField) (v : V),
          (g : V →ₗ[ZMod 2] V) (x • v) = x • (g : V →ₗ[ZMod 2] V) v) ∨
        (∀ (x : OmegaField) (v : V),
          (g : V →ₗ[ZMod 2] V) (x • v) = x ^ 2 • (g : V →ₗ[ZMod 2] V) v)) ∧
    (∀ e : V ≃+ V, ((∀ (x : OmegaField) (v : V), e (x • v) = x • e v) ∨
        (∀ (x : OmegaField) (v : V), e (x • v) = x ^ 2 • e v)) →
      ∃ g ∈ Subgroup.normalizer
          (Subgroup.zpowers z : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)),
        ∀ v, (g : V →ₗ[ZMod 2] V) v = e v) ∧
    (∀ g : LinearMap.GeneralLinearGroup (ZMod 2) V, g * z * g⁻¹ = z ^ 2 ↔
      ∀ (x : OmegaField) (v : V),
        (g : V →ₗ[ZMod 2] V) (x • v) = x ^ 2 • (g : V →ₗ[ZMod 2] V) v) := by
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hcent := commute_iff_omega_linear hω
  have hsig := conj_eq_sq_iff_semilinear hω
  have hnorm : ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) V,
      g ∈ Subgroup.normalizer
          (Subgroup.zpowers z : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) ↔
        (∀ (x : OmegaField) (v : V),
          (g : V →ₗ[ZMod 2] V) (x • v) = x • (g : V →ₗ[ZMod 2] V) v) ∨
        (∀ (x : OmegaField) (v : V),
          (g : V →ₗ[ZMod 2] V) (x • v) = x ^ 2 • (g : V →ₗ[ZMod 2] V) v) := by
    intro g
    rw [← hcent, ← hsig, ← mul_inv_eq_iff_eq_mul]
    exact ⟨conj_eq_or_eq_sq_of_mem_normalizer hz, mem_normalizer_zpowers_of_conj hz3⟩
  refine ⟨?_, hcent, fun e => ?_, hnorm, fun e he => ?_, hsig⟩
  · rw [← Module.finrank_mul_finrank (ZMod 2) OmegaField V, finrank_omegaField]
  · refine ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv (e.restrictScalars (ZMod 2)),
      fun v => rfl, ?_⟩
    rw [hcent]
    intro x v
    exact e.map_smul x v
  ·
    have hlin : ∀ (c : ZMod 2) (v : V), e (c • v) = c • e v := by
      intro c v
      have hc2 : (algebraMap (ZMod 2) OmegaField c) ^ 2 = algebraMap (ZMod 2) OmegaField c := by
        rw [← map_pow]
        congr 1
        revert c
        decide
      rcases he with h | h
      · rw [← algebraMap_smul OmegaField c v, h, algebraMap_smul]
      · rw [← algebraMap_smul OmegaField c v, h, hc2, algebraMap_smul]
    let g := LinearMap.GeneralLinearGroup.ofLinearEquiv (e.toLinearEquiv hlin)
    have hg : ∀ v, (g : V →ₗ[ZMod 2] V) v = e v := fun v => rfl
    refine ⟨g, (hnorm g).2 ?_, hg⟩
    rcases he with h | h
    · exact Or.inl fun x v => by rw [hg, hg, h]
    · exact Or.inr fun x v => by rw [hg, hg, h]

end Structure

end CFSG.LinearAlgebra
