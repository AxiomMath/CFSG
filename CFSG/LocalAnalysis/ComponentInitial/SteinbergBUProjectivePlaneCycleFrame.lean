module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneTorusCentralizer

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Matrix.ProjGenLinGroup

variable {K : Type*} [Field K] {p : ℕ} [NeZero p] (P : GL (Fin p) K) {ζ : Kˣ}

omit [NeZero p] in
theorem torusHom_mem_centralizer (x : Fin p → Kˣ) :
    torusHom P x ∈ Subgroup.centralizer {frameElt P ζ} := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.1 hy]
  exact torusHom_comm P _ _

omit [NeZero p] in
theorem mk_mem_centralizer_of_rel {M : GL (Fin p) K} {c : Kˣ}
    (h : (P⁻¹ * M * P) * TauCeti.diagGL (rootVec ζ) =
      GeneralLinearGroup.scalar (Fin p) c * (TauCeti.diagGL (rootVec ζ) * (P⁻¹ * M * P))) :
    mk M ∈ Subgroup.centralizer {frameElt P ζ} := by
  have h2 : M * (P * TauCeti.diagGL (rootVec ζ) * P⁻¹) = GeneralLinearGroup.scalar (Fin p) c *
      ((P * TauCeti.diagGL (rootVec ζ) * P⁻¹) * M) := by
    calc M * (P * TauCeti.diagGL (rootVec ζ) * P⁻¹) =
        P * ((P⁻¹ * M * P) * TauCeti.diagGL (rootVec ζ)) * P⁻¹ := by group
      _ = P * GeneralLinearGroup.scalar (Fin p) c *
          (TauCeti.diagGL (rootVec ζ) * (P⁻¹ * M * P)) * P⁻¹ := by rw [h]; group
      _ = GeneralLinearGroup.scalar (Fin p) c * P *
          (TauCeti.diagGL (rootVec ζ) * (P⁻¹ * M * P)) * P⁻¹ := by rw [mul_scalar_comm c P]
      _ = _ := by group
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.1 hy]
  change mk (P * TauCeti.diagGL (rootVec ζ) * P⁻¹) * mk M =
    mk M * mk (P * TauCeti.diagGL (rootVec ζ) * P⁻¹)
  rw [← map_mul, ← map_mul, h2, map_mul mk (GeneralLinearGroup.scalar (Fin p) c), mk_scalar,
    one_mul]

theorem frameScalar_eq_of_rel {M : GL (Fin p) K} {c : Kˣ}
    (h : (P⁻¹ * M * P) * TauCeti.diagGL (rootVec ζ) =
      GeneralLinearGroup.scalar (Fin p) c * (TauCeti.diagGL (rootVec ζ) * (P⁻¹ * M * P))) :
    frameScalar P ζ ⟨mk M, mk_mem_centralizer_of_rel P h⟩ = c :=
  (frameScalar_mk P ζ ⟨M, mk_mem_centralizer_of_rel P h⟩).trans
    (frameScalarFun_eq P ζ ⟨M, mk_mem_centralizer_of_rel P h⟩ h)

theorem frameScalar_torusHom (x : Fin p → Kˣ) :
    frameScalar P ζ ⟨torusHom P x, torusHom_mem_centralizer P x⟩ = 1 := by
  have h : (P⁻¹ * (P * TauCeti.diagGL x * P⁻¹) * P) * TauCeti.diagGL (rootVec ζ) =
      GeneralLinearGroup.scalar (Fin p) 1 *
        (TauCeti.diagGL (rootVec ζ) * (P⁻¹ * (P * TauCeti.diagGL x * P⁻¹) * P)) := by
    rw [map_one, one_mul, show P⁻¹ * (P * TauCeti.diagGL x * P⁻¹) * P = TauCeti.diagGL x by group,
      ← map_mul, ← map_mul, mul_comm]
  exact frameScalar_eq_of_rel P h

theorem frameScalar_pow (y : Subgroup.centralizer {frameElt P ζ}) : frameScalar P ζ y ^ p = 1 := by
  obtain ⟨M, rfl⟩ := exists_framePre P ζ y
  rw [frameScalar_mk]
  have h := frameScalarHat_spec P ζ M
  generalize P⁻¹ * (M : GL (Fin p) K) * P = N at h
  generalize TauCeti.diagGL (rootVec ζ) = D at h
  have hs : Matrix.GeneralLinearGroup.det
      (GeneralLinearGroup.scalar (Fin p) (frameScalarHat P ζ M)) = frameScalarHat P ζ M ^ p := by
    ext
    simp
  have h2 := congrArg Matrix.GeneralLinearGroup.det (eq_mul_inv_of_mul_eq h.symm)
  simp only [map_mul, map_inv] at h2
  rw [hs, mul_comm (Matrix.GeneralLinearGroup.det D), mul_inv_cancel] at h2
  exact h2

variable {W : GL (Fin p) K}
  (hW : W * TauCeti.diagGL (rootVec ζ) =
    GeneralLinearGroup.scalar (Fin p) ζ⁻¹ * (TauCeti.diagGL (rootVec ζ) * W))

omit [NeZero p] in
include hW in
theorem cycle_rel : (P⁻¹ * (P * W * P⁻¹) * P) * TauCeti.diagGL (rootVec ζ) =
    GeneralLinearGroup.scalar (Fin p) ζ⁻¹ *
      (TauCeti.diagGL (rootVec ζ) * (P⁻¹ * (P * W * P⁻¹) * P)) := by
  rw [show P⁻¹ * (P * W * P⁻¹) * P = W by group]
  exact hW

omit [NeZero p] in
include hW in
theorem mk_cycle_mem_centralizer : mk (P * W * P⁻¹) ∈ Subgroup.centralizer {frameElt P ζ} :=
  mk_mem_centralizer_of_rel P (cycle_rel P hW)

include hW in
theorem frameScalar_cycle :
    frameScalar P ζ ⟨mk (P * W * P⁻¹), mk_cycle_mem_centralizer P hW⟩ = ζ⁻¹ :=
  frameScalar_eq_of_rel P (cycle_rel P hW)

omit [NeZero p] in
theorem cycleElt_pow (hWp : W ^ p = 1) : mk (P * W * P⁻¹) ^ p = 1 := by
  rw [← map_pow, conj_pow, hWp, mul_one, mul_inv_cancel, map_one]

include hW in
theorem orderOf_cycleElt (hp : p.Prime) (hζ : IsPrimitiveRoot (ζ : K) p) (hWp : W ^ p = 1) :
    orderOf (mk (P * W * P⁻¹)) = p := by
  have := Fact.mk hp
  refine orderOf_eq_prime (cycleElt_pow P hWp) fun h1 => ?_
  have h2 := frameScalar_cycle P hW
  have h3 : (⟨mk (P * W * P⁻¹), mk_cycle_mem_centralizer P hW⟩ :
      Subgroup.centralizer {frameElt P ζ}) = 1 := Subtype.ext h1
  rw [h3, map_one] at h2
  have h4 : ζ = 1 := inv_eq_one.1 h2.symm
  exact hζ.ne_one hp.one_lt (by rw [h4, Units.val_one])

include hW in
theorem exists_torus_mul_pow (hζ : IsPrimitiveRoot (ζ : K) p)
    (y : Subgroup.centralizer {frameElt P ζ}) :
    ∃ (x : Fin p → Kˣ) (k : ℕ), (y : ProjGenLinGroup (Fin p) K) =
      torusHom P x * mk (P * W * P⁻¹) ^ k := by
  obtain ⟨w, hw1, hw2⟩ : ∃ w : Subgroup.centralizer {frameElt P ζ},
      (w : ProjGenLinGroup (Fin p) K) = mk (P * W * P⁻¹) ∧ frameScalar P ζ w = ζ⁻¹ :=
    ⟨_, rfl, frameScalar_cycle P hW⟩
  have hζi : IsPrimitiveRoot (((ζ⁻¹ : Kˣ) : K)) p := by
    rw [Units.val_inv_eq_inv_val]
    exact hζ.inv
  obtain ⟨k, -, hk⟩ := hζi.eq_pow_of_pow_eq_one (ξ := ((frameScalar P ζ y : Kˣ) : K)) (by
    rw [← Units.val_pow_eq_pow_val, frameScalar_pow P y, Units.val_one])
  have hk' : frameScalar P ζ (y * (w ^ k)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow, hw2, mul_inv_eq_one]
    exact (Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hk)).symm
  obtain ⟨x, hx⟩ := mem_torus_of_frameScalar hζ _ hk'
  refine ⟨x, k, ?_⟩
  rw [hx, Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow, hw1, inv_mul_cancel_right]

include hW in
theorem eq_one_of_zpow_mem_torus (hζ : IsPrimitiveRoot (ζ : K) p) (hWp : W ^ p = 1) {k : ℤ}
    (hk : mk (P * W * P⁻¹) ^ k ∈ (torusHom P).range) : mk (P * W * P⁻¹) ^ k = 1 := by
  obtain ⟨w, hw1, hw2⟩ : ∃ w : Subgroup.centralizer {frameElt P ζ},
      (w : ProjGenLinGroup (Fin p) K) = mk (P * W * P⁻¹) ∧ frameScalar P ζ w = ζ⁻¹ :=
    ⟨_, rfl, frameScalar_cycle P hW⟩
  obtain ⟨x, hx⟩ := hk
  have h1 : (⟨torusHom P x, torusHom_mem_centralizer P x⟩ : Subgroup.centralizer {frameElt P ζ}) =
      w ^ k := Subtype.ext (by rw [SubgroupClass.coe_zpow, hw1]; exact hx)
  have h2 := frameScalar_torusHom P (ζ := ζ) x
  rw [h1, map_zpow, hw2] at h2
  have hζi : IsPrimitiveRoot (ζ⁻¹ : Kˣ) p := (IsPrimitiveRoot.coe_units_iff.1 hζ).inv
  obtain ⟨m, rfl⟩ := (hζi.zpow_eq_one_iff_dvd k).1 h2
  rw [zpow_mul, zpow_natCast, cycleElt_pow P hWp, one_zpow]

theorem conj_mem_torus (hζ : IsPrimitiveRoot (ζ : K) p) (y : Subgroup.centralizer {frameElt P ζ})
    (x : Fin p → Kˣ) :
    (y : ProjGenLinGroup (Fin p) K) * torusHom P x * (y : ProjGenLinGroup (Fin p) K)⁻¹ ∈
      (torusHom P).range := by
  have h : frameScalar P ζ (y * ⟨torusHom P x, torusHom_mem_centralizer P x⟩ * y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, frameScalar_torusHom, mul_one, mul_inv_cancel]
  obtain ⟨x', hx'⟩ := mem_torus_of_frameScalar hζ _ h
  exact ⟨x', hx'⟩

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
