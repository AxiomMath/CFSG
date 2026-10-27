module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6E16
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6Gauss

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CatFactsSp4

namespace Cat7E6

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

variable {K : Type} [Field K]

abbrev mat (X : gsp 2 K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  ((X : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

theorem gsp_ext {X Y : gsp 2 K} (h : mat X = mat Y) : X = Y := Subtype.ext (Units.ext h)

theorem mat_mul (X Y : gsp 2 K) : mat (X * Y) = mat X * mat Y := rfl

theorem mat_one : mat (1 : gsp 2 K) = 1 := rfl

theorem mat_mul_mat_inv (X : gsp 2 K) : mat X * mat X⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem mat_inv_mul_mat (X : gsp 2 K) : mat X⁻¹ * mat X = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem conj_eq_of_mat {A X Y : gsp 2 K} (h : mat A * mat X = mat Y * mat A) :
    conjAut 2 K A * conjAut 2 K X * (conjAut 2 K A)⁻¹ = conjAut 2 K Y := by
  have h1 : A * X = Y * A := gsp_ext (by rw [mat_mul, mat_mul]; exact h)
  rw [← map_mul, h1, map_mul, mul_inv_cancel_right]

theorem det_gaussEmb (z : Gauss K) : (gaussEmb z).det = QuadraticAlgebra.norm z := by
  rw [gaussEmb_eq, det_fin_two_of, norm_eq]
  ring

theorem dm_gaussEmb (z : Gauss K) : dm * gaussEmb z = gaussEmb (star z) * dm := by
  rw [gaussEmb_eq, gaussEmb_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dm, Matrix.mul_apply, Fin.sum_univ_two]

theorem gaussEmb_comm (z w : Gauss K) : gaussEmb z * gaussEmb w = gaussEmb w * gaussEmb z := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem gaussEmb_smul (c : K) (z : Gauss K) : gaussEmb (c • z) = c • gaussEmb z := map_smul _ _ _

theorem blk_smul (c : K) (g h : Matrix (Fin 2) (Fin 2) K) : blk (c • g) (c • h) = c • blk g h := by
  simp only [blk, diag2, Matrix.smul_apply, smul_eq_mul, Matrix.fromBlocks_smul]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem blk_eq_smul_one_iff (c : K) (g h : Matrix (Fin 2) (Fin 2) K) :
    blk g h = c • 1 ↔ g = c • 1 ∧ h = c • 1 := by
  rw [show (c • 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = blk (c • 1) (c • 1) by
    rw [blk_smul, blk_one_one]]
  exact ⟨blk_injective _ _ _ _, fun ⟨h1, h2⟩ => by rw [h1, h2]⟩

theorem blk_similitude {g h : Matrix (Fin 2) (Fin 2) K} {μ : K} (hg : g.det = μ) (hh : h.det = μ) :
    (blk g h)ᵀ * formJ 2 K * blk g h = μ • formJ 2 K := by
  rw [formJ_eq_blk, blk_transpose, blk_mul, blk_mul,
    show gᵀ * J₁ * g = g.det • J₁ from transpose_mul_J₁_mul g,
    show hᵀ * J₁ * h = h.det • J₁ from transpose_mul_J₁_mul h, hg, hh, blk_smul]

theorem wm_diag2 (a b : K) : wm * diag2 a b * wm = diag2 b a := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [wm, diag2, Matrix.mul_apply, Fin.sum_univ_two]

theorem swap_blk (g h : Matrix (Fin 2) (Fin 2) K) :
    kron 1 wm * blk g h * kron 1 wm = blk h g := by
  have hk : kron (1 : Matrix (Fin 2) (Fin 2) K) wm = fromBlocks wm 0 0 wm := by
    simp [kron]
  rw [hk, blk, blk, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, wm_diag2]

@[expose] def iotaU : (Gauss K)ˣ →* GL (Fin 2) K :=
  Units.map (gaussEmb (K := K)).toRingHom.toMonoidHom

@[expose] def blkHom :
    Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K
    where
  toFun x := blk x.1 x.2
  map_one' := blk_one_one
  map_mul' x y := (blk_mul x.1 x.2 y.1 y.2).symm

@[expose] def torGL : (Gauss K)ˣ × (Gauss K)ˣ →* GL (Fin 2 ⊕ Fin 2) K :=
  (Units.map blkHom).comp ((MulEquiv.prodUnits.symm.toMonoidHom).comp (iotaU.prodMap iotaU))

theorem coe_torGL (x : (Gauss K)ˣ × (Gauss K)ˣ) :
    ((torGL x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      blk (gaussEmb (x.1 : Gauss K)) (gaussEmb (x.2 : Gauss K)) := rfl

@[expose] def normU : (Gauss K)ˣ →* Kˣ :=
  Units.map (QuadraticAlgebra.norm (R := K) (a := -1) (b := 0))

theorem coe_normU (x : (Gauss K)ˣ) : ((normU x : Kˣ) : K) = QuadraticAlgebra.norm (x : Gauss K) :=
  rfl

@[expose] def torSub (K : Type) [Field K] : Subgroup ((Gauss K)ˣ × (Gauss K)ˣ) :=
  MonoidHom.eqLocus (normU.comp (MonoidHom.fst _ _)) (normU.comp (MonoidHom.snd _ _))

theorem mem_torSub {x : (Gauss K)ˣ × (Gauss K)ˣ} :
    x ∈ torSub K ↔
      QuadraticAlgebra.norm (x.1 : Gauss K) = QuadraticAlgebra.norm (x.2 : Gauss K) := by
  change normU x.1 = normU x.2 ↔ _
  rw [Units.ext_iff]
  rfl

theorem torGL_mem_gsp (x : torSub K) : torGL (x : (Gauss K)ˣ × (Gauss K)ˣ) ∈ gsp 2 K :=
  ⟨normU (x : (Gauss K)ˣ × (Gauss K)ˣ).1, by
    rw [coe_torGL, coe_normU]
    exact blk_similitude (det_gaussEmb _) ((det_gaussEmb _).trans (mem_torSub.mp x.2).symm)⟩

@[expose] def torG : torSub K →* gsp 2 K :=
  (torGL.comp (torSub K).subtype).codRestrict (gsp 2 K) torGL_mem_gsp

theorem mat_torG (x : torSub K) :
    mat (torG x) = blk (gaussEmb ((x : (Gauss K)ˣ × (Gauss K)ˣ).1 : Gauss K))
      (gaussEmb ((x : (Gauss K)ˣ × (Gauss K)ˣ).2 : Gauss K)) := rfl

@[expose] def cT : torSub K →* MulAut (StatedProj (StatedSp 2 K)) := (conjAut 2 K).comp torG

theorem gaussEmb_eq_smul_one_iff (c : K) (z : Gauss K) :
    gaussEmb z = c • 1 ↔ z = algebraMap K (Gauss K) c := by
  rw [← gaussEmb_algebraMap]
  exact gaussEmb_injective.eq_iff

theorem cT_eq_one_iff [Finite K] (x : torSub K) :
    cT x = 1 ↔ ∃ c : K, ((x : (Gauss K)ˣ × (Gauss K)ˣ).1 : Gauss K) = algebraMap K (Gauss K) c ∧
      ((x : (Gauss K)ˣ × (Gauss K)ˣ).2 : Gauss K) = algebraMap K (Gauss K) c := by
  rw [cT, MonoidHom.comp_apply, conjAut_eq_one_iff]
  constructor
  · rintro ⟨c, hc⟩
    have h := Units.ext_iff.mp hc
    change mat (torG x) = _ at h
    rw [mat_torG, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, blk_eq_smul_one_iff, gaussEmb_eq_smul_one_iff,
      gaussEmb_eq_smul_one_iff] at h
    exact ⟨c, h⟩
  · rintro ⟨c, h1, h2⟩
    have hc : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at h1
      exact ((x : (Gauss K)ˣ × (Gauss K)ˣ).1).ne_zero h1
    refine ⟨Units.mk0 c hc, Units.ext ?_⟩
    change mat (torG x) = _
    rw [mat_torG, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, blk_eq_smul_one_iff, gaussEmb_eq_smul_one_iff,
      gaussEmb_eq_smul_one_iff]
    exact ⟨h1, h2⟩

section Weyl

variable (v : (Gauss K)ˣ) (hv : QuadraticAlgebra.norm (v : Gauss K) = -1)

@[expose] def sig1 : gsp 2 K :=
  gspOf (blk dm (gaussEmb (v : Gauss K))) (-1) (by
    rw [Units.val_neg, Units.val_one]
    exact blk_similitude det_dm ((det_gaussEmb _).trans hv))

theorem mat_sig1 : mat (sig1 v hv) = blk dm (gaussEmb (v : Gauss K)) := rfl

abbrev swp : gsp 2 K := x1W

theorem mat_swp : mat (swp (K := K)) = kron 1 wm := rfl

theorem swp_mul_swp : (swp : gsp 2 K) * swp = 1 := by
  apply gsp_ext
  rw [mat_mul, mat_swp, kron_mul, Matrix.one_mul, wm_mul_wm, kron_one_one, mat_one]

@[expose] def w3 : gsp 2 K := sig1 v hv * swp

theorem sig1_tor (x : torSub K) (y : torSub K)
    (hy : (y : (Gauss K)ˣ × (Gauss K)ˣ) = (starU (x : (Gauss K)ˣ × (Gauss K)ˣ).1,
      (x : (Gauss K)ˣ × (Gauss K)ˣ).2)) :
    mat (sig1 v hv) * mat (torG x) = mat (torG y) * mat (sig1 v hv) := by
  rw [mat_sig1, mat_torG, mat_torG, hy, blk_mul, blk_mul, dm_gaussEmb, gaussEmb_comm]
  rfl

theorem swp_tor (x : torSub K) (y : torSub K)
    (hy : (y : (Gauss K)ˣ × (Gauss K)ˣ) = ((x : (Gauss K)ˣ × (Gauss K)ˣ).2,
      (x : (Gauss K)ˣ × (Gauss K)ˣ).1)) :
    mat swp * mat (torG x) = mat (torG y) * mat swp := by
  have h := swap_blk (gaussEmb (((x : (Gauss K)ˣ × (Gauss K)ˣ).1 : (Gauss K)ˣ) : Gauss K))
    (gaussEmb (((x : (Gauss K)ˣ × (Gauss K)ˣ).2 : (Gauss K)ˣ) : Gauss K))
  rw [mat_swp, mat_torG, mat_torG, hy]
  calc kron 1 wm * blk (gaussEmb _) (gaussEmb _) =
      kron 1 wm * blk (gaussEmb _) (gaussEmb _) * kron 1 wm * kron 1 wm := by
        rw [Matrix.mul_assoc _ (kron 1 wm), kron_mul, Matrix.one_mul, wm_mul_wm, kron_one_one,
          Matrix.mul_one]
    _ = _ := by rw [h]

theorem w3_tor (x y z : torSub K)
    (hy : (y : (Gauss K)ˣ × (Gauss K)ˣ) = ((x : (Gauss K)ˣ × (Gauss K)ˣ).2,
      (x : (Gauss K)ˣ × (Gauss K)ˣ).1))
    (hz : (z : (Gauss K)ˣ × (Gauss K)ˣ) = (starU (y : (Gauss K)ˣ × (Gauss K)ˣ).1,
      (y : (Gauss K)ˣ × (Gauss K)ˣ).2)) :
    mat (w3 v hv) * mat (torG x) = mat (torG z) * mat (w3 v hv) := by
  rw [w3, mat_mul, Matrix.mul_assoc, swp_tor x y hy, ← Matrix.mul_assoc,
    sig1_tor v hv y z hz, Matrix.mul_assoc]

theorem dm_mul_gaussEmb_sq (z : Gauss K) :
    dm * gaussEmb z * (dm * gaussEmb z) = gaussEmb (star z * z) := by
  have h := dm_gaussEmb z
  calc dm * gaussEmb z * (dm * gaussEmb z) = dm * gaussEmb z * dm * gaussEmb z := by
        rw [Matrix.mul_assoc (dm * gaussEmb z)]
    _ = gaussEmb (star z) * dm * dm * gaussEmb z := by rw [h]
    _ = gaussEmb (star z) * gaussEmb z := by
        rw [Matrix.mul_assoc (gaussEmb (star z)) dm dm, dm_mul_dm, Matrix.mul_one]
    _ = gaussEmb (star z * z) := (map_mul _ _ _).symm

theorem gaussEmb_mul_dm_sq (z : Gauss K) :
    gaussEmb z * dm * (gaussEmb z * dm) = gaussEmb (z * star z) := by
  have h := dm_gaussEmb z
  calc gaussEmb z * dm * (gaussEmb z * dm) = gaussEmb z * (dm * gaussEmb z) * dm := by
        simp only [Matrix.mul_assoc]
    _ = gaussEmb z * (gaussEmb (star z) * dm) * dm := by rw [h]
    _ = gaussEmb z * gaussEmb (star z) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, dm_mul_dm, Matrix.mul_one]
    _ = gaussEmb (z * star z) := (map_mul _ _ _).symm

include hv in
theorem gaussEmb_norm_neg : gaussEmb (star (v : Gauss K) * (v : Gauss K)) = (-1 : K) • 1 := by
  rw [mul_comm, mul_star_eq_norm, hv, gaussEmb_algebraMap]

theorem mat_w3_sq : mat (w3 v hv * w3 v hv) =
    blk (dm * gaussEmb (v : Gauss K)) (gaussEmb (v : Gauss K) * dm) := by
  have h1 : mat swp * mat (sig1 v hv) * mat swp = blk (gaussEmb (v : Gauss K)) dm := by
    rw [mat_swp, mat_sig1]
    exact swap_blk _ _
  simp only [w3, mat_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (mat swp), h1, mat_sig1, blk_mul]

theorem mat_w3_pow_four : mat ((w3 v hv * w3 v hv) * (w3 v hv * w3 v hv)) = (-1 : K) • 1 := by
  rw [mat_mul, mat_w3_sq, blk_mul, dm_mul_gaussEmb_sq, gaussEmb_mul_dm_sq,
    mul_comm (v : Gauss K), gaussEmb_norm_neg v hv, blk_smul, blk_one_one]

theorem mat_sig1_sq :
    mat (sig1 v hv * sig1 v hv) = blk 1 (gaussEmb ((v : Gauss K) * (v : Gauss K))) := by
  rw [mat_mul, mat_sig1, blk_mul, dm_mul_dm, map_mul]

end Weyl

end Cat7E6

end CFSG.ComponentClassification.GSThmB
