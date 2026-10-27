module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryIsometry

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryIsometry

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

universe u v w

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {sigma : K ≃+* K} (h : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K)

@[expose] def isometryGroup : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x y, h (g x) (g y) = h x y}
  one_mem' := by intro x y; rfl
  mul_mem' {g j} hg hj := by
    intro x y
    exact (hg (j x) (j y)).trans (hj x y)
  inv_mem' {g} hg := by
    intro x y
    have hh := hg (g.symm x) (g.symm y)
    simpa only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using hh.symm

theorem mem_isometryGroup_iff (g : V ≃ₗ[K] V) :
    g ∈ isometryGroup h ↔ ∀ x y, h (g x) (g y) = h x y := Iff.rfl

@[expose] def isometryDeterminant : isometryGroup h →* Kˣ :=
  LinearEquiv.det.comp (isometryGroup h).subtype

abbrev specialIsometry : Subgroup (isometryGroup h) := (isometryDeterminant h).ker

theorem mem_specialIsometry_iff (g : isometryGroup h) :
    g ∈ specialIsometry h ↔ LinearMap.det g.val.toLinearMap = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  change (LinearEquiv.det g.val : K) = 1 ↔ LinearMap.det g.val.toLinearMap = 1
  rw [LinearEquiv.coe_det]

instance isometryDeterminantQuotientComm :
    IsMulCommutative (isometryGroup h ⧸ specialIsometry h) := by
  let e := QuotientGroup.quotientKerEquivRange (isometryDeterminant h)
  exact isMulCommutative_iff.mpr (fun x y => e.injective (by
    rw [map_mul, map_mul, mul_comm]))

variable {W : Type w} [AddCommGroup W] [Module K W]
  (k : W →ₛₗ[sigma.toRingHom] W →ₗ[K] K)

@[expose] def formIsometryGroupEquiv (e : V ≃ₗ[K] W)
    (he : ∀ x y, k (e x) (e y) = h x y) : isometryGroup h ≃* isometryGroup k where
  toFun g := ⟨(e.symm.trans g.val).trans e, by
    intro x y
    change k (e (g.val (e.symm x))) (e (g.val (e.symm y))) = k x y
    rw [he, g.property, ← he, e.apply_symm_apply, e.apply_symm_apply]⟩
  invFun g := ⟨(e.trans g.val).trans e.symm, by
    intro x y
    change h (e.symm (g.val (e x))) (e.symm (g.val (e y))) = h x y
    rw [← he, e.apply_symm_apply, e.apply_symm_apply, g.property, he]⟩
  left_inv g := by
    apply Subtype.ext
    ext x
    simp
  right_inv g := by
    apply Subtype.ext
    ext x
    simp
  map_mul' g j := by
    apply Subtype.ext
    ext x
    simp

theorem formIsometryGroupEquiv_apply (e : V ≃ₗ[K] W)
    (he : ∀ x y, k (e x) (e y) = h x y) (g : isometryGroup h) (x : W) :
    (formIsometryGroupEquiv h k e he g).val x = e (g.val (e.symm x)) := rfl

theorem formIsometryGroupEquiv_determinant (e : V ≃ₗ[K] W)
    (he : ∀ x y, k (e x) (e y) = h x y) (g : isometryGroup h) :
    isometryDeterminant k (formIsometryGroupEquiv h k e he g) = isometryDeterminant h g :=
  LinearEquiv.det_conj g.val e

@[expose] def formSpecialIsometryEquiv (e : V ≃ₗ[K] W)
    (he : ∀ x y, k (e x) (e y) = h x y) : specialIsometry h ≃* specialIsometry k where
  toFun g := ⟨formIsometryGroupEquiv h k e he g.val, by
    rw [MonoidHom.mem_ker, formIsometryGroupEquiv_determinant]
    exact g.property⟩
  invFun g := ⟨(formIsometryGroupEquiv h k e he).symm g.val, by
    rw [MonoidHom.mem_ker]
    rw [← formIsometryGroupEquiv_determinant h k e he,
      MulEquiv.apply_symm_apply]
    exact g.property⟩
  left_inv g := Subtype.ext ((formIsometryGroupEquiv h k e he).symm_apply_apply g.val)
  right_inv g := Subtype.ext ((formIsometryGroupEquiv h k e he).apply_symm_apply g.val)
  map_mul' g j := Subtype.ext ((formIsometryGroupEquiv h k e he).map_mul g.val j.val)

theorem formSpecialIsometryEquiv_val (e : V ≃ₗ[K] W)
    (he : ∀ x y, k (e x) (e y) = h x y) (g : specialIsometry h) :
    (formSpecialIsometryEquiv h k e he g).val = formIsometryGroupEquiv h k e he g.val := rfl

variable {n : ℕ}

theorem isometry_iff_Uid (b : Module.Basis (Fin n) K V)
    (hb : ∀ i j, h (b i) (b j) = if i = j then 1 else 0) (g : V ≃ₗ[K] V) :
    g ∈ isometryGroup h ↔
      CatalogueBAlternatingIsometry.basisMatrixEquiv b g ∈ Uid sigma n := by
  rw [mem_isometryGroup_iff]
  constructor
  · intro hg x y
    obtain ⟨x, rfl⟩ := b.equivFun.surjective x
    obtain ⟨y, rfl⟩ := b.equivFun.surjective y
    rw [CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec,
      CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec,
      ← CatalogueBHermitian.form_eq_herm_coordinates h b hb,
      ← CatalogueBHermitian.form_eq_herm_coordinates h b hb]
    exact hg x y
  · intro hg x y
    rw [CatalogueBHermitian.form_eq_herm_coordinates h b hb,
      CatalogueBHermitian.form_eq_herm_coordinates h b hb]
    rw [← CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec,
      ← CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec]
    exact hg (b.equivFun x) (b.equivFun y)

@[expose] def isometryMatrixEquiv (b : Module.Basis (Fin n) K V)
    (hb : ∀ i j, h (b i) (b j) = if i = j then 1 else 0) :
    isometryGroup h ≃* Uid sigma n where
  toFun g := ⟨CatalogueBAlternatingIsometry.basisMatrixEquiv b g.val,
    (isometry_iff_Uid h b hb g.val).mp g.property⟩
  invFun A := ⟨(CatalogueBAlternatingIsometry.basisMatrixEquiv b).symm A.val,
    (isometry_iff_Uid h b hb _).mpr (by
      rw [MulEquiv.apply_symm_apply]
      exact A.property)⟩
  left_inv g := Subtype.ext ((CatalogueBAlternatingIsometry.basisMatrixEquiv b).symm_apply_apply g.val)
  right_inv A := Subtype.ext ((CatalogueBAlternatingIsometry.basisMatrixEquiv b).apply_symm_apply A.val)
  map_mul' g j := Subtype.ext ((CatalogueBAlternatingIsometry.basisMatrixEquiv b).map_mul g.val j.val)

theorem isometryMatrixEquiv_val (b : Module.Basis (Fin n) K V)
    (hb : ∀ i j, h (b i) (b j) = if i = j then 1 else 0) (g : isometryGroup h) :
    (isometryMatrixEquiv h b hb g).val = CatalogueBAlternatingIsometry.basisMatrixEquiv b g.val := rfl

theorem isometryMatrixEquiv_determinant (b : Module.Basis (Fin n) K V)
    (hb : ∀ i j, h (b i) (b j) = if i = j then 1 else 0) (g : isometryGroup h) :
    determinant sigma n (isometryMatrixEquiv h b hb g) = isometryDeterminant h g := by
  apply Units.ext
  change (CatalogueBAlternatingIsometry.basisMatrixEquiv b g.val).val.det =
    (LinearEquiv.det g.val : K)
  rw [CatalogueBAlternatingIsometry.basisMatrixEquiv_val,
    LinearMap.det_toMatrix, LinearEquiv.coe_det]

@[expose] def specialIsometryMatrixEquiv (b : Module.Basis (Fin n) K V)
    (hb : ∀ i j, h (b i) (b j) = if i = j then 1 else 0) :
    specialIsometry h ≃* SUid sigma n :=
  ({ toFun := fun g => ⟨isometryMatrixEquiv h b hb g.val, by
       rw [MonoidHom.mem_ker, isometryMatrixEquiv_determinant]
       exact g.property⟩
     invFun := fun A => ⟨(isometryMatrixEquiv h b hb).symm A.val, by
       rw [MonoidHom.mem_ker, ← isometryMatrixEquiv_determinant h b hb,
         MulEquiv.apply_symm_apply]
       exact A.property⟩
     left_inv := fun g => Subtype.ext ((isometryMatrixEquiv h b hb).symm_apply_apply g.val)
     right_inv := fun A => Subtype.ext ((isometryMatrixEquiv h b hb).apply_symm_apply A.val)
     map_mul' := fun g j => Subtype.ext ((isometryMatrixEquiv h b hb).map_mul g.val j.val) } :
       specialIsometry h ≃* specialUnitary sigma n).trans (specialUnitaryEquivSUid sigma n)

theorem exists_native_isometry_groups [Finite K] [FiniteDimensional K V]
    (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      (∀ i j, h (b i) (b j) = if i = j then 1 else 0) ∧
      Nonempty (isometryGroup h ≃* Uid sigma (Module.finrank K V)) ∧
      Nonempty (specialIsometry h ≃* SUid sigma (Module.finrank K V)) := by
  obtain ⟨b, hb⟩ := CatalogueBHermitian.exists_orthonormal_basis h hsym hnd hsigma hne
  exact ⟨b, hb, ⟨isometryMatrixEquiv h b hb⟩, ⟨specialIsometryMatrixEquiv h b hb⟩⟩

end CFSG.ComponentClassification.CatalogueBUnitaryIsometry
