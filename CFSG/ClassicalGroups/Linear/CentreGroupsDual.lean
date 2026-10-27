module

public import CFSG.ClassicalGroups.Linear.CentreGroups

public section

namespace CFSG.ClassicalGroups.Linear.Model

open Matrix CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LargeExtraspecial.S4
open scoped MatrixGroups

theorem det_inverseTranspose_eq_one {n : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    (hg : (g : Matrix (Fin n) (Fin n) K).det = 1) :
    (Matrix.GeneralLinearGroup.inverseTranspose g : Matrix (Fin n) (Fin n) K).det = 1 := by
  have h : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det *
      (g : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, Matrix.det_transpose]
  rw [hg, mul_one] at h
  exact h

theorem inverseTranspose_mem_statedSL {n : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    (hg : g ∈ StatedSL n K) : Matrix.GeneralLinearGroup.inverseTranspose g ∈ StatedSL n K :=
  StatedAPI.mem_statedSL_iff.mpr (det_inverseTranspose_eq_one (StatedAPI.mem_statedSL_iff.mp hg))

theorem inverseTranspose_one_add_vecMulVec {n : ℕ} {K : Type} [Field K] {x y : Fin n → K}
    (hyx : y ⬝ᵥ x = 0) {g : GL (Fin n) K}
    (hg : (g : Matrix (Fin n) (Fin n) K) = 1 + vecMulVec x y) :
    ((Matrix.GeneralLinearGroup.inverseTranspose g : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 + vecMulVec y (-x) := by
  have hinv : (1 + vecMulVec x y)⁻¹ = 1 + vecMulVec x (-y) := by
    apply Matrix.inv_eq_right_inv
    rw [one_add_vecMulVec_mul_center n K x y (-y) hyx, add_neg_cancel, vecMulVec_zero,
      add_zero]
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, Matrix.coe_units_inv, hg, hinv,
    Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_vecMulVec,
    Matrix.neg_vecMulVec, Matrix.vecMulVec_neg]

theorem inverseTranspose_mem_transvCenter {n : ℕ} {K : Type} [Field K] (a : Fin n → K)
    {g : GL (Fin n) K} (hg : g ∈ transvAxis n K a) :
    Matrix.GeneralLinearGroup.inverseTranspose g ∈ transvCenter n K a := by
  obtain ⟨v, hv, hgv⟩ := hg
  refine ⟨-v, ?_, inverseTranspose_one_add_vecMulVec hv hgv⟩
  rw [neg_dotProduct, dotProduct_comm, hv, neg_zero]

theorem inverseTranspose_mem_transvAxis {n : ℕ} {K : Type} [Field K] (a : Fin n → K)
    {h : GL (Fin n) K} (hh : h ∈ transvCenter n K a) :
    Matrix.GeneralLinearGroup.inverseTranspose h ∈ transvAxis n K a := by
  obtain ⟨b, hb, hhb⟩ := hh
  refine ⟨-b, ?_, ?_⟩
  · rw [dotProduct_neg, dotProduct_comm, hb, neg_zero]
  · rw [inverseTranspose_one_add_vecMulVec hb hhb, Matrix.vecMulVec_neg, Matrix.neg_vecMulVec]

theorem mem_transvAxis_iff_inverseTranspose {n : ℕ} {K : Type} [Field K] (a : Fin n → K)
    (g : GL (Fin n) K) :
    g ∈ transvAxis n K a ↔ Matrix.GeneralLinearGroup.inverseTranspose g ∈ transvCenter n K a :=
  ⟨inverseTranspose_mem_transvCenter a, fun hg => by
    have h := inverseTranspose_mem_transvAxis a hg
    rwa [Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose] at h⟩

theorem mem_center_mulEquiv_iff {G : Type*} [Group G] (e : G ≃* G) (g : G) :
    g ∈ Subgroup.center G ↔ e g ∈ Subgroup.center G := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro hg k
    have h := congrArg e (hg (e.symm k))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h
  · intro hg k
    apply e.injective
    simpa only [map_mul] using hg (e k)

theorem mem_statedScalars_inverseTranspose {n : ℕ} {K : Type} [Field K] (g : GL (Fin n) K) :
    g ∈ StatedScalars (Fin n) K ↔
      Matrix.GeneralLinearGroup.inverseTranspose g ∈ StatedScalars (Fin n) K := by
  rw [StatedAPI.statedScalars_eq_center]
  exact mem_center_mulEquiv_iff Matrix.GeneralLinearGroup.inverseTranspose g

@[expose] def dualSL (n : ℕ) (K : Type) [Field K] : StatedSL n K ≃* StatedSL n K where
  toFun g := ⟨Matrix.GeneralLinearGroup.inverseTranspose (g : GL (Fin n) K),
    inverseTranspose_mem_statedSL g.2⟩
  invFun g := ⟨Matrix.GeneralLinearGroup.inverseTranspose (g : GL (Fin n) K),
    inverseTranspose_mem_statedSL g.2⟩
  left_inv g := Subtype.ext (Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose
    (g : GL (Fin n) K))
  right_inv g := Subtype.ext (Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose
    (g : GL (Fin n) K))
  map_mul' g h := Subtype.ext (map_mul Matrix.GeneralLinearGroup.inverseTranspose
    (g : GL (Fin n) K) (h : GL (Fin n) K))

section Dual

variable {n : ℕ} {K : Type} [Field K]

theorem map_dualSL_subgroupOf {U V : Subgroup (GL (Fin n) K)}
    (h : ∀ g : GL (Fin n) K, g ∈ U ↔ Matrix.GeneralLinearGroup.inverseTranspose g ∈ V) :
    (U.subgroupOf (StatedSL n K)).map (dualSL n K).toMonoidHom =
      V.subgroupOf (StatedSL n K) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (h _).mp hy
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hx' : Matrix.GeneralLinearGroup.inverseTranspose
        (Matrix.GeneralLinearGroup.inverseTranspose (x : GL (Fin n) K)) ∈ V := by
      rw [Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose]
      exact hx
    refine ⟨dualSL n K x, ?_, Subtype.ext
      (Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose (x : GL (Fin n) K))⟩
    rw [Subgroup.mem_subgroupOf]
    exact (h _).mpr hx'

theorem map_dualSL_axis (a : Fin n → K) :
    ((transvAxis n K a).subgroupOf (StatedSL n K)).map (dualSL n K).toMonoidHom =
      (transvCenter n K a).subgroupOf (StatedSL n K) :=
  map_dualSL_subgroupOf (mem_transvAxis_iff_inverseTranspose a)

theorem dualSL_scalars :
    ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)).map (dualSL n K).toMonoidHom =
      (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) :=
  map_dualSL_subgroupOf mem_statedScalars_inverseTranspose

end Dual

@[expose] def dualProj (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL n K) ≃* StatedProj (StatedSL n K) :=
  QuotientGroup.congr ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))
    ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) (dualSL n K) dualSL_scalars

theorem exists_dualEquiv (n : ℕ) (K : Type) [Field K] :
    ∃ δ : StatedProj (StatedSL n K) ≃* StatedProj (StatedSL n K),
      ∀ a : Fin n → K,
        (transvImage n K (transvAxis n K a)).map δ.toMonoidHom = cg n K a := by
  refine ⟨dualProj n K, fun a => ?_⟩
  have hcomp : (dualProj n K).toMonoidHom.comp
      (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))) =
      (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))).comp
        (dualSL n K).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  unfold cg transvImage
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, map_dualSL_axis]

end CFSG.ClassicalGroups.Linear.Model
