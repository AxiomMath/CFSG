module

public import CFSG.LieType.SeitzGeneration.OmegaF2.Basic
public import CFSG.LieType.SeitzGeneration.RootPairOrthBlock

public section

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.RootPairOrth Matrix

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

structure PerpData (P P' : HypPair Q) (r : V) : Prop where
  Q_r : Q r = 0
  e : polar Q r P.e = 0
  f : polar Q r P.f = 0
  e' : polar Q r P'.e = 0
  f' : polar Q r P'.f = 0

variable {P P' : HypPair Q}

theorem PerpData.polar_quadEmb {r : V} (hr : PerpData P P' r) (X : Matrix (Fin 2) (Fin 2) K) :
    polar Q r (quadEmb P P' X) = 0 := by
  simp only [quadEmb, LinearMap.coe_mk, AddHom.coe_mk, polar_add_right, polar_smul_right_eq,
    polar_neg_right, hr.e, hr.f, hr.e', hr.f', mul_zero, neg_zero, add_zero]

theorem eichler_quadEmb_add {r : V} (hr : PerpData P P' r) (X X' : Matrix (Fin 2) (Fin 2) K) :
    eichler Q r (quadEmb P P' X) * eichler Q r (quadEmb P P' X') =
      eichler Q r (quadEmb P P' (X + X')) := by
  rw [eichler_mul (hr.polar_quadEmb X) (hr.polar_quadEmb X'), map_add]

private theorem quadEmb_Q_eq_det (h : P.Orth P') (Y : Matrix (Fin 2) (Fin 2) K) :
    Q (quadEmb P P' Y) = Matrix.det Y := by
  have hu1 : Q (Y 0 0 • P.e + Y 1 1 • P.f) = Y 0 0 * Y 1 1 := by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, P.Q_e, P.Q_f,
      polar_smul_left_eq, polar_smul_right_eq, P.polar_ef]
    ring
  have hu2 : Q (Y 0 1 • (-P'.e) + Y 1 0 • P'.f) = -(Y 0 1 * Y 1 0) := by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, QuadraticMap.map_neg, P'.Q_e,
      P'.Q_f, polar_smul_left_eq, polar_smul_right_eq, polar_neg_left, P'.polar_ef]
    ring
  have hcross : polar Q (Y 0 0 • P.e + Y 1 1 • P.f) (Y 0 1 • (-P'.e) + Y 1 0 • P'.f) = 0 := by
    simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
      polar_neg_right, h.ee, h.ef, h.fe, h.ff, mul_zero, neg_zero, add_zero]
  rw [Matrix.det_fin_two]
  show Q ((Y 0 0 • P.e + Y 1 1 • P.f) + (Y 0 1 • (-P'.e) + Y 1 0 • P'.f)) = _
  rw [QuadraticMap.map_add Q, hu1, hu2, hcross]
  ring

private theorem quadHom_apply_eq_add (h : P.Orth P') (A : SpecialLinearGroup (Fin 2) K) (v : V) :
    quadHom h A v = quadEmb P P' ((A : Matrix (Fin 2) (Fin 2) K) * quadProj P P' v) +
      (v - quadEmb P P' (quadProj P P' v)) := by
  rw [quadHom_apply, sub_mul, one_mul, map_sub]
  abel

theorem quadHom_mem_orthogonalGroup (h : P.Orth P') (A : SpecialLinearGroup (Fin 2) K) :
    quadHom h A ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  obtain ⟨w, hw⟩ : ∃ w : V, w = v - quadEmb P P' (quadProj P P' v) := ⟨_, rfl⟩
  have hv : v = quadEmb P P' (quadProj P P' v) + w := by
    rw [hw]
    abel
  have hact : quadHom h A v =
      quadEmb P P' ((A : Matrix (Fin 2) (Fin 2) K) * quadProj P P' v) + w := by
    rw [hw]
    exact quadHom_apply_eq_add h A v
  have hw0 : quadProj P P' w = 0 := by
    rw [hw, map_sub, quadProj_emb h, sub_self]
  have he : polar Q w P.e = 0 := by
    simpa [quadProj] using congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) hw0
  have hf : polar Q w P.f = 0 := by
    simpa [quadProj] using congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hw0
  have he' : polar Q w P'.e = 0 := by
    simpa [quadProj] using congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hw0
  have hf' : polar Q w P'.f = 0 := by
    simpa [quadProj] using congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hw0
  have hwpol : ∀ Y : Matrix (Fin 2) (Fin 2) K, polar Q (quadEmb P P' Y) w = 0 := fun Y => by
    rw [polar_comm Q (quadEmb P P' Y) w]
    simp only [quadEmb, LinearMap.coe_mk, AddHom.coe_mk, polar_add_right, polar_smul_right_eq,
      polar_neg_right, he, hf, he', hf', mul_zero, neg_zero, add_zero]
  have hdecomp : ∀ Y : Matrix (Fin 2) (Fin 2) K,
      Q (quadEmb P P' Y + w) = Q (quadEmb P P' Y) + Q w := fun Y => by
    rw [QuadraticMap.map_add Q (quadEmb P P' Y) w, hwpol Y, add_zero]
  calc Q (quadHom h A v)
      = Q (quadEmb P P' ((A : Matrix (Fin 2) (Fin 2) K) * quadProj P P' v) + w) := by
        rw [hact]
    _ = Q (quadEmb P P' ((A : Matrix (Fin 2) (Fin 2) K) * quadProj P P' v)) + Q w :=
        hdecomp _
    _ = Matrix.det ((A : Matrix (Fin 2) (Fin 2) K) * quadProj P P' v) + Q w := by
        rw [quadEmb_Q_eq_det h]
    _ = Matrix.det (quadProj P P' v) + Q w := by
        rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul]
    _ = Q (quadEmb P P' (quadProj P P' v)) + Q w := by
        rw [quadEmb_Q_eq_det h]
    _ = Q (quadEmb P P' (quadProj P P' v) + w) := (hdecomp _).symm
    _ = Q v := by rw [← hv]

theorem quadHom_apply_perp (h : P.Orth P') {r : V} (hr : PerpData P P' r)
    (A : SpecialLinearGroup (Fin 2) K) : quadHom h A r = r := by
  have hp : quadProj P P' r = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [quadProj, hr.e, hr.f, hr.e', hr.f']
  rw [quadHom_apply, hp, mul_zero, map_zero, add_zero]

theorem quadHom_apply_quadEmb (h : P.Orth P') (A : SpecialLinearGroup (Fin 2) K)
    (X : Matrix (Fin 2) (Fin 2) K) :
    quadHom h A (quadEmb P P' X) = quadEmb P P' ((A : Matrix (Fin 2) (Fin 2) K) * X) := by
  rw [quadHom_apply, quadProj_emb h, ← map_add]
  congr 1
  rw [sub_mul, one_mul]
  abel

theorem quadHom_conj_eichler_quadEmb (h : P.Orth P') {r : V} (hr : PerpData P P' r)
    (A : SpecialLinearGroup (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    quadHom h A * eichler Q r (quadEmb P P' X) * (quadHom h A)⁻¹ =
      eichler Q r (quadEmb P P' ((A : Matrix (Fin 2) (Fin 2) K) * X)) := by
  rw [eichler_conj (quadHom_mem_orthogonalGroup h A), quadHom_apply_perp h hr,
    quadHom_apply_quadEmb h]

theorem theta_mul (h : P.Orth P') {r : V} (hr : PerpData P P' r)
    (X X' : Matrix (Fin 2) (Fin 2) K) (A A' : SpecialLinearGroup (Fin 2) K) :
    (eichler Q r (quadEmb P P' X) * quadHom h A) * (eichler Q r (quadEmb P P' X') * quadHom h A') =
      eichler Q r (quadEmb P P' (X + (A : Matrix (Fin 2) (Fin 2) K) * X')) * quadHom h (A * A') := by
  calc (eichler Q r (quadEmb P P' X) * quadHom h A) * (eichler Q r (quadEmb P P' X') * quadHom h A')
      = eichler Q r (quadEmb P P' X) * (quadHom h A * eichler Q r (quadEmb P P' X') * (quadHom h A)⁻¹) *
          (quadHom h A * quadHom h A') := by group
    _ = eichler Q r (quadEmb P P' X) *
          eichler Q r (quadEmb P P' ((A : Matrix (Fin 2) (Fin 2) K) * X')) *
          (quadHom h A * quadHom h A') := by rw [quadHom_conj_eichler_quadEmb h hr]
    _ = eichler Q r (quadEmb P P' (X + (A : Matrix (Fin 2) (Fin 2) K) * X')) *
          (quadHom h A * quadHom h A') := by rw [eichler_quadEmb_add hr]
    _ = eichler Q r (quadEmb P P' (X + (A : Matrix (Fin 2) (Fin 2) K) * X')) *
          quadHom h (A * A') := by rw [map_mul]

@[expose] def twistSet (h : P.Orth P') (r : V) (H : Subgroup (V ≃ₗ[K] V)) :
    Set (Matrix (Fin 2) (Fin 2) K × SpecialLinearGroup (Fin 2) K) :=
  {p | eichler Q r (quadEmb P P' p.1) * quadHom h p.2 ∈ H}

theorem twistSet_closed (h : P.Orth P') {r : V} (hr : PerpData P P' r)
    (H : Subgroup (V ≃ₗ[K] V)) : TwistClosed (twistSet h r H) := by
  refine ⟨?_, ?_, ?_⟩
  · show eichler Q r (quadEmb P P' 0) * quadHom h 1 ∈ H
    rw [map_zero, eichler_zero_right, map_one, one_mul]
    exact H.one_mem
  · intro X X' A A' hXA hXA'
    simp only [twistSet, Set.mem_setOf_eq] at hXA hXA' ⊢
    rw [← theta_mul h hr X X' A A']
    exact H.mul_mem hXA hXA'
  · intro X A hXA
    simp only [twistSet, Set.mem_setOf_eq] at hXA ⊢
    have hAA : (A : Matrix (Fin 2) (Fin 2) K) *
        ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h0 : X + (A : Matrix (Fin 2) (Fin 2) K) *
        -(((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X) = 0 := by
      rw [Matrix.mul_neg, ← mul_assoc, hAA, one_mul, add_neg_cancel]
    have hprod := theta_mul h hr X
      (-(((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X)) A A⁻¹
    rw [h0, map_zero, eichler_zero_right, mul_inv_cancel, map_one, one_mul] at hprod
    rw [← inv_eq_of_mul_eq_one_right hprod]
    exact H.inv_mem hXA

end CFSG.LieType.SeitzGeneration.OmegaF2
