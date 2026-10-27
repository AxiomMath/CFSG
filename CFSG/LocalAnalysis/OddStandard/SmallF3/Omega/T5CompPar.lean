module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermField

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

private theorem even_finrank_ker_add_one_of_det_eq_one {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : V →ₗ[K] V) (hf : f * f = 1)
    (hdet : LinearMap.det f = 1) (hneg : (-1 : K) ≠ 1) :
    Even (Module.finrank K (LinearMap.ker (f + 1))) := by
  have h2 : (2 : K) ≠ 0 := by
    rw [← one_add_one_eq_two]
    exact fun h => hneg (neg_eq_iff_add_eq_zero.mpr h)
  have hff : ∀ v : V, f (f v) = v := by
    intro v
    have h := congr($hf v)
    simpa [Module.End.mul_apply] using h
  let Vp : Submodule K V := LinearMap.ker (f - 1)
  let W : Submodule K V := LinearMap.ker (f + 1)
  have hcompl : IsCompl Vp W := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff_inf_le]
      intro v hv
      rw [Submodule.mem_bot]
      have hv1 : f v = v := by
        have h := (Submodule.mem_inf.mp hv).1
        change v ∈ LinearMap.ker (f - 1) at h
        rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
        exact h
      have hv2 : f v = -v := by
        have h := (Submodule.mem_inf.mp hv).2
        change v ∈ LinearMap.ker (f + 1) at h
        rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
          add_eq_zero_iff_eq_neg] at h
        exact h
      have hvv : v = -v := hv1.symm.trans hv2
      have h2v : (2 : K) • v = 0 := by
        rw [two_smul]
        exact eq_neg_iff_add_eq_zero.mp hvv
      calc v = ((2 : K)⁻¹ * 2) • v := by rw [inv_mul_cancel₀ h2, one_smul]
        _ = (2 : K)⁻¹ • ((2 : K) • v) := by rw [smul_smul]
        _ = 0 := by rw [h2v, smul_zero]
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro v
      have hv : (2 : K)⁻¹ • (v + f v) + (2 : K)⁻¹ • (v - f v) = v := by
        rw [← smul_add]
        have hsum : (v + f v) + (v - f v) = (2 : K) • v := by
          rw [two_smul]
          abel
        rw [hsum, smul_smul, inv_mul_cancel₀ h2, one_smul]
      rw [← hv]
      apply Submodule.add_mem_sup
      · change (2 : K)⁻¹ • (v + f v) ∈ LinearMap.ker (f - 1)
        rw [LinearMap.mem_ker]
        have hz : (f - 1) (v + f v) = 0 := by
          rw [LinearMap.sub_apply, Module.End.one_apply, LinearMap.map_add, hff v]
          abel
        rw [LinearMap.map_smul, hz, smul_zero]
      · change (2 : K)⁻¹ • (v - f v) ∈ LinearMap.ker (f + 1)
        rw [LinearMap.mem_ker]
        have hz : (f + 1) (v - f v) = 0 := by
          rw [LinearMap.add_apply, Module.End.one_apply, LinearMap.map_sub, hff v]
          abel
        rw [LinearMap.map_smul, hz, smul_zero]
  let P : (Vp × W) ≃ₗ[K] V := Submodule.prodEquivOfIsCompl Vp W hcompl
  have hcomp : ((P.symm : V →ₗ[K] (Vp × W)) ∘ₗ f ∘ₗ (P : (Vp × W) →ₗ[K] V))
      = LinearMap.prodMap (LinearMap.id : Vp →ₗ[K] Vp)
          ((-1 : K) • (LinearMap.id : W →ₗ[K] W)) := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, y⟩ := z
    have hx : f (x : V) = x := by
      have h := x.2
      change (x : V) ∈ LinearMap.ker (f - 1) at h
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
      exact h
    have hy : f (y : V) = -y := by
      have h := y.2
      change (y : V) ∈ LinearMap.ker (f + 1) at h
      rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
        add_eq_zero_iff_eq_neg] at h
      exact h
    have hPxy : (P : (Vp × W) →ₗ[K] V) (x, y) = (x : V) + (y : V) := by
      change (P : (Vp × W) ≃ₗ[K] V) (x, y) = (x : V) + (y : V)
      exact Submodule.coe_prodEquivOfIsCompl' Vp W hcompl (x, y)
    have hPxy' : (P : (Vp × W) →ₗ[K] V) (x, -y) = (x : V) + -(y : V) := by
      change (P : (Vp × W) ≃ₗ[K] V) (x, -y) = (x : V) + -(y : V)
      exact Submodule.coe_prodEquivOfIsCompl' Vp W hcompl (x, -y)
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.id_coe, id_eq,
      LinearMap.smul_apply, Module.End.one_apply, neg_one_smul]
    rw [hPxy, LinearMap.map_add, hx, hy, ← hPxy']
    change (P.symm : V ≃ₗ[K] (Vp × W)) (P (x, -y)) = (x, -y)
    exact LinearEquiv.symm_apply_apply P (x, -y)
  have hdet' : LinearMap.det f = (-1 : K) ^ Module.finrank K W := by
    have hconj := LinearMap.det_conj (f := f) (e := P.symm)
    rw [show ((P.symm).symm : (Vp × W) →ₗ[K] V) = (P : (Vp × W) →ₗ[K] V) from rfl] at hconj
    rw [hcomp] at hconj
    rw [← hconj, LinearMap.det_prodMap, LinearMap.det_smul]
    simp
  have hpow : (-1 : K) ^ Module.finrank K W = 1 := by
    rw [← hdet', hdet]
  exact (neg_one_pow_eq_one_iff_even hneg).mp hpow

theorem t5_cplx_perfect_parity {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {A : Type} [Group A] (ρ : A →* (V ≃ₗ[ZMod 3] V))
    (c : V ≃ₗ[ZMod 3] V) (hc : ∀ v, c (c v) = -v) (hcomm : ∀ a v, ρ a (c v) = c (ρ a v))
    {P : Subgroup A} (hP : Group.IsPerfect ↥P) {a : A} (ha : a ∈ P)
    (ha2 : ∀ v, ρ a (ρ a v) = v) (W : Submodule (ZMod 3) V)
    (hW : ∀ v, v ∈ W ↔ ρ a v = -v) : Module.finrank (ZMod 3) W % 4 = 0 := by
  let u : Module.End (ZMod 3) V := (c : V →ₗ[ZMod 3] V)
  have hu : u * u = (-1 : ZMod 3) • (1 : Module.End (ZMod 3) V) + (0 : ZMod 3) • u := by
    ext v
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, zero_smul, add_zero]
    change c (c v) = (-1 : ZMod 3) • v
    rw [hc v]
    simp
  let f9 : F9 →ₐ[ZMod 3] Module.End (ZMod 3) V := QuadraticAlgebra.lift ⟨u, hu⟩
  letI : Module F9 V := Module.compHom V f9.toRingHom
  haveI : IsScalarTower (ZMod 3) F9 V := by
    refine IsScalarTower.of_algebraMap_smul fun r x => ?_
    show f9 (algebraMap (ZMod 3) F9 r) x = r • x
    rw [f9.commutes]
    simp [Algebra.algebraMap_eq_smul_one]
  haveI : FiniteDimensional F9 V :=
    Module.Finite.of_restrictScalars_finite (ZMod 3) F9 V
  have hf9_apply (z : F9) :
      f9 z = z.re • (1 : Module.End (ZMod 3) V) + z.im • u := by
    rw [QuadraticAlgebra.lift_apply_apply]
  have hf9_omega : f9 (QuadraticAlgebra.omega : F9) = u := by
    rw [hf9_apply]
    simp
  have homega : ∀ v : V, (QuadraticAlgebra.omega : F9) • v = c v := by
    intro v
    show f9 (QuadraticAlgebra.omega : F9) v = c v
    rw [hf9_omega]
    rfl
  have hsmul_eq : ∀ (z : F9) (v : V), z • v = z.re • v + z.im • c v := by
    intro z v
    show f9 z v = z.re • v + z.im • c v
    rw [hf9_apply]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    rfl
  let hrho9 (x : A) : V →ₗ[F9] V :=
    { toFun := fun v => ρ x v
      map_add' := fun v w => (ρ x).map_add v w
      map_smul' := fun z v => by
        show ρ x (f9 z v) = f9 z (ρ x v)
        rw [hf9_apply z]
        simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
        rw [(ρ x).map_add, (ρ x).map_smul, (ρ x).map_smul]
        change z.re • ρ x v + z.im • ρ x (c v) = z.re • ρ x v + z.im • c (ρ x v)
        rw [hcomm x v] }
  have hrho9_apply (x : A) (v : V) : hrho9 x v = ρ x v := rfl
  let hrho9_equiv (x : A) : V ≃ₗ[F9] V :=
    LinearEquiv.ofBijective (hrho9 x) (by
      have h : ⇑(hrho9 x) = ⇑(ρ x) := funext (hrho9_apply x)
      rw [h]
      exact (ρ x).bijective)
  have hrho9_equiv_apply (x : A) (v : V) : (hrho9_equiv x) v = ρ x v := by
    change hrho9 x v = ρ x v
    exact hrho9_apply x v
  let rho9 : A →* (V ≃ₗ[F9] V) :=
    { toFun := fun x => hrho9_equiv x
      map_one' := by
        ext v
        rw [hrho9_equiv_apply 1 v, map_one]
        rfl
      map_mul' := by
        intro x y
        ext v
        rw [hrho9_equiv_apply (x * y) v, map_mul]
        change ρ x (ρ y v) = (hrho9_equiv x) ((hrho9_equiv y) v)
        rw [hrho9_equiv_apply y v, hrho9_equiv_apply x (ρ y v)] }
  let δ : A →* F9ˣ := (LinearEquiv.det : (V ≃ₗ[F9] V) →* F9ˣ).comp rho9
  have hda : δ a = 1 := by
    haveI : Group.IsPerfect ↥P := hP
    have h := Abelianization.commutator_subset_ker (δ.comp P.subtype)
    simp only [Group.IsPerfect.commutator_eq_top] at h
    have hmem := h (Subgroup.mem_top (⟨a, ha⟩ : ↥P))
    rw [MonoidHom.mem_ker] at hmem
    simpa using hmem
  have hf_det : LinearMap.det (hrho9 a) = 1 := by
    have h2 : ((LinearEquiv.det (rho9 a) : F9ˣ) : F9) = 1 := by
      rw [show LinearEquiv.det (rho9 a) = δ a from rfl, hda]
      rfl
    rw [LinearEquiv.coe_det] at h2
    have hmap : (rho9 a : V →ₗ[F9] V) = hrho9 a :=
      LinearMap.ext fun v => hrho9_equiv_apply a v
    rwa [hmap] at h2
  have hff : hrho9 a * hrho9 a = 1 := by
    ext v
    rw [Module.End.mul_apply, hrho9_apply a (hrho9 a v), hrho9_apply a v,
      Module.End.one_apply]
    exact ha2 v
  have hneg : (-1 : F9) ≠ 1 := by
    haveI : Fact (2 < 3) := ⟨by norm_num⟩
    exact CharP.neg_one_ne_one F9 3
  have heven : Even (Module.finrank F9 (LinearMap.ker (hrho9 a + 1))) :=
    even_finrank_ker_add_one_of_det_eq_one (hrho9 a) hff hf_det hneg
  have hW9 : ∀ v, v ∈ LinearMap.ker (hrho9 a + 1) ↔ ρ a v = -v := by
    intro v
    simp only [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
      add_eq_zero_iff_eq_neg, hrho9_apply a v]
  have hWeq : (LinearMap.ker (hrho9 a + 1)).restrictScalars (ZMod 3) = W := by
    ext v
    rw [Submodule.restrictScalars_mem, hW9 v, hW v]
  have htower : Module.finrank (ZMod 3) W
      = 2 * Module.finrank F9 (LinearMap.ker (hrho9 a + 1)) := by
    rw [← hWeq]
    rw [← Module.finrank_mul_finrank (ZMod 3) F9
      ((LinearMap.ker (hrho9 a + 1)).restrictScalars (ZMod 3))]
    rw [finrank_F9]
    rfl
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp heven
  rw [htower, hk]
  have h4 : 2 * (2 * k) = 4 * k := by ring
  rw [h4]
  exact Nat.mod_eq_zero_of_dvd (dvd_mul_right 4 k)

end CFSG.OddStandard.SmallF3.Omega
