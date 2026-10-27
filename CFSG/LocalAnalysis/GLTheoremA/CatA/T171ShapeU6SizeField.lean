module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Det

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Matrix Polynomial
open CFSG.RankThree.PartOne.KCPrimary

theorem commutator_eq_one_of_fieldType {K : Type} [Field K]
    {l ζ : Kˣ} {M Y Z : GL (Fin 6) K}
    (hM3 : M ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) l)
    (hl : ∀ c : Kˣ, c ^ 3 ≠ l)
    (hYM : Y * M = M * Y) (hZM : Z * M = M * Z)
    (hcomm : Y * Z * Y⁻¹ * Z⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) ζ)
    (hζ3 : ζ ^ 3 = 1) : ζ = 1 := by
  classical
  have hc : ∀ d : K, d ^ 3 ≠ (l : K) := by
    intro d hd
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hd
      exact l.ne_zero hd.symm
    exact hl (Units.mk0 d hd0) (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hd]))
  set a : K[X] := X ^ 3 - C (l : K) with ha
  haveI : Fact (Irreducible a) :=
    ⟨CFSG.StandardType.Line63.H5.irreducible_X_pow_three_sub_C_of_not_cube hc⟩
  set x : Module.End K (Fin 6 → K) := Matrix.toLin' (M : Matrix (Fin 6) (Fin 6) K) with hx
  have hM3' : (M : Matrix (Fin 6) (Fin 6) K) ^ 3 = Matrix.scalar (Fin 6) (l : K) := by
    rw [← Units.val_pow_eq_pow_val, hM3, Matrix.GeneralLinearGroup.coe_scalar]
  have hax : aeval x a = 0 := by
    rw [ha, map_sub, map_pow, aeval_X, aeval_C, hx, ← Matrix.toLin'_pow, hM3', sub_eq_zero]
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Module.algebraMap_end_apply, Matrix.scalar_apply]
    funext i
    rw [Matrix.mulVec_diagonal]
    rfl
  have htop : primaryComponent x a = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [mem_primaryComponent, hax]
    rfl
  have hfin : Module.finrank K (primaryComponent x a) = 6 := by
    rw [htop, finrank_top]
    simp
  have hdeg : a.natDegree = 3 := natDegree_X_pow_sub_C
  have hm : Module.finrank (AdjoinRoot a) (primaryComponent x a) = 2 := by
    have h := finrank_primaryComponent x a
    rw [hfin, hdeg] at h
    omega
  have hYc : Commute (Matrix.toLin' ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) x := by
    rw [Commute, SemiconjBy, hx, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← Units.val_mul, ← Units.val_mul, hYM]
  have hZc : Commute (Matrix.toLin' ((Z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) x := by
    rw [Commute, SemiconjBy, hx, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← Units.val_mul, ← Units.val_mul, hZM]
  have hYi : Y⁻¹ * M = M * Y⁻¹ := by
    calc Y⁻¹ * M = Y⁻¹ * M * Y * Y⁻¹ := by group
      _ = Y⁻¹ * (M * Y) * Y⁻¹ := by group
      _ = Y⁻¹ * (Y * M) * Y⁻¹ := by rw [hYM]
      _ = M * Y⁻¹ := by group
  have hZi : Z⁻¹ * M = M * Z⁻¹ := by
    calc Z⁻¹ * M = Z⁻¹ * M * Z * Z⁻¹ := by group
      _ = Z⁻¹ * (M * Z) * Z⁻¹ := by group
      _ = Z⁻¹ * (Z * M) * Z⁻¹ := by rw [hZM]
      _ = M * Z⁻¹ := by group
  have hYim : ((Y⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        ((Y⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    have h := congrArg Units.val hYi
    rw [Units.val_mul, Units.val_mul] at h
    exact h
  have hZim : ((Z⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        ((Z⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    have h := congrArg Units.val hZi
    rw [Units.val_mul, Units.val_mul] at h
    exact h
  have hYic : Commute (Matrix.toLin' (((Y⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))) x := by
    rw [Commute, SemiconjBy, hx, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hYim]
  have hZic : Commute (Matrix.toLin' (((Z⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))) x := by
    rw [Commute, SemiconjBy, hx, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hZim]
  let y : commutant x :=
    ⟨Matrix.toLin' ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K), (mem_commutant x).mpr hYc⟩
  let z : commutant x :=
    ⟨Matrix.toLin' ((Z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K), (mem_commutant x).mpr hZc⟩
  let yi : commutant x :=
    ⟨Matrix.toLin' (((Y⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)),
      (mem_commutant x).mpr hYic⟩
  let zi : commutant x :=
    ⟨Matrix.toLin' (((Z⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)),
      (mem_commutant x).mpr hZic⟩
  have hYmat : ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      ((Y⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    have h := congrArg Units.val (mul_inv_cancel Y)
    rw [Units.val_mul] at h
    exact h
  have hZmat : ((Z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      ((Z⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    have h := congrArg Units.val (mul_inv_cancel Z)
    rw [Units.val_mul] at h
    exact h
  have hyy : y * yi = 1 := by
    apply Subtype.ext
    show Matrix.toLin' ((Y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      Matrix.toLin' (((Y⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) = 1
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hYmat, Matrix.toLin'_one]
    rfl
  have hzz : z * zi = 1 := by
    apply Subtype.ext
    show Matrix.toLin' ((Z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      Matrix.toLin' (((Z⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) = 1
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hZmat, Matrix.toLin'_one]
    rfl
  let Ye : Module.End (AdjoinRoot a) (primaryComponent x a) := commutantRestrictHom a y
  let Ze : Module.End (AdjoinRoot a) (primaryComponent x a) := commutantRestrictHom a z
  let Yie : Module.End (AdjoinRoot a) (primaryComponent x a) := commutantRestrictHom a yi
  let Zie : Module.End (AdjoinRoot a) (primaryComponent x a) := commutantRestrictHom a zi
  have hYmul : Ye * Yie = 1 := by
    rw [show Ye * Yie = commutantRestrictHom a (y * yi) by
      simp [Ye, Yie, map_mul]]
    rw [hyy, map_one]
  have hZmul : Ze * Zie = 1 := by
    rw [show Ze * Zie = commutantRestrictHom a (z * zi) by
      simp [Ze, Zie, map_mul]]
    rw [hzz, map_one]
  have hdetY : LinearMap.det Ye * LinearMap.det Yie = 1 := by
    rw [← map_mul, hYmul, map_one]
  have hdetZ : LinearMap.det Ze * LinearMap.det Zie = 1 := by
    rw [← map_mul, hZmul, map_one]
  set T : Module.End K (Fin 6 → K) :=
    Matrix.toLin' (((Y * Z * Y⁻¹ * Z⁻¹ : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K) with hTdef
  have hTscalar : T = (ζ : K) • (1 : Module.End K (Fin 6 → K)) := by
    rw [hTdef, hcomm]
    ext v i
    simp [Matrix.toLin'_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_mulVec, Module.algebraMap_end_apply, Pi.single_apply]
  have hTmul : T = y.1 * z.1 * yi.1 * zi.1 := by
    rw [hTdef]
    simp only [y, z, yi, zi, Units.val_mul, Units.val_inv_eq_inv_val, Matrix.toLin'_mul,
      Module.End.mul_eq_comp]
  have hTcomm : T ∈ commutant x := by
    rw [hTmul]
    exact mul_mem (mul_mem (mul_mem y.2 z.2) yi.2) zi.2
  have hTeq : commutantRestrictHom a ⟨T, hTcomm⟩ = Ye * Ze * Yie * Zie := by
    rw [show (⟨T, hTcomm⟩ : commutant x) = y * z * yi * zi from Subtype.ext hTmul]
    simp only [Ye, Ze, Yie, Zie, map_mul]
  have hTE : commutantRestrictHom a ⟨T, hTcomm⟩ =
      (ζ : K) • (1 : Module.End (AdjoinRoot a) (primaryComponent x a)) := by
    ext v i
    simp only [coe_commutantRestrictHom]
    rw [hTscalar]
    simp [LinearMap.smul_apply, Submodule.coe_smul]
  have hdet_comm : LinearMap.det (Ye * Ze * Yie * Zie) = 1 := by
    rw [map_mul, map_mul, map_mul]
    calc LinearMap.det Ye * LinearMap.det Ze * LinearMap.det Yie * LinearMap.det Zie
        = (LinearMap.det Ye * LinearMap.det Yie) *
            (LinearMap.det Ze * LinearMap.det Zie) := by ring
      _ = 1 := by rw [hdetY, hdetZ, mul_one]
  have hdet_scalar : LinearMap.det
      ((ζ : K) • (1 : Module.End (AdjoinRoot a) (primaryComponent x a))) =
      (algebraMap K (AdjoinRoot a) (ζ : K)) ^ 2 := by
    rw [show (ζ : K) • (1 : Module.End (AdjoinRoot a) (primaryComponent x a)) =
        (algebraMap K (AdjoinRoot a) (ζ : K)) •
          (1 : Module.End (AdjoinRoot a) (primaryComponent x a)) from by
      rw [IsScalarTower.algebraMap_smul]]
    rw [LinearMap.det_smul, map_one, mul_one, hm]
  have hζ2K : (ζ : K) ^ 2 = 1 := by
    have h1 : LinearMap.det (commutantRestrictHom a ⟨T, hTcomm⟩) = 1 := by
      rw [hTeq]
      exact hdet_comm
    rw [hTE, hdet_scalar, ← map_pow] at h1
    exact (algebraMap K (AdjoinRoot a)).injective (by rw [map_one]; exact h1)
  have hζ2 : ζ ^ 2 = 1 := Units.ext (by simpa using hζ2K)
  have hζ1 : ζ = 1 := by
    have h := hζ3
    rw [pow_succ, hζ2, one_mul] at h
    exact h
  exact hζ1

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
