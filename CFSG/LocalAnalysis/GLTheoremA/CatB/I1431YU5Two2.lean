module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5Ker
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherParabolicData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem mulVec_mem_of_isoStab {h : UnitaryFieldData 2 1 K} {W : Submodule K (HypIndex 2 1 → K)}
    {g : hypSU h 2 1} (hg : g ∈ isoStabilizer h 2 1 W) {w : HypIndex 2 1 → K} (hw : w ∈ W) :
    ((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ w ∈ W := by
  have hs : g • W = W := MulAction.mem_stabilizer_iff.mp hg
  have hs' : (g : GL (HypIndex 2 1) K) • W = W := hs
  have hmem : ((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ w ∈
      (g : GL (HypIndex 2 1) K) • W := by
    rw [smul_eq_map]
    exact ⟨w, hw, rfl⟩
  rwa [hs'] at hmem

@[expose] noncomputable def resW {W : Submodule K (HypIndex 2 1 → K)} (x : GL (HypIndex 2 1) K)
    (hx : ∀ w ∈ W, (x : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ w ∈ W) : W →ₗ[K] W :=
  LinearMap.restrict (Matrix.mulVecLin (x : Matrix (HypIndex 2 1) (HypIndex 2 1) K)) hx

theorem resW_apply {W : Submodule K (HypIndex 2 1 → K)} (x : GL (HypIndex 2 1) K)
    (hx : ∀ w ∈ W, (x : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ w ∈ W) (w : W) :
    ((resW x hx w : W) : HypIndex 2 1 → K) = (x : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ (w : HypIndex 2 1 → K) :=
  rfl

theorem resW_mul {W : Submodule K (HypIndex 2 1 → K)} {x y : GL (HypIndex 2 1) K}
    (hx : ∀ w ∈ W, (x : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ w ∈ W)
    (hy : ∀ w ∈ W, (y : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ w ∈ W)
    (hxy : ∀ w ∈ W, ((x * y : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ w ∈ W) :
    resW (x * y) hxy = resW x hx * resW y hy := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  rw [Module.End.mul_apply, resW_apply, resW_apply, resW_apply, Units.val_mul,
    Matrix.mulVec_mulVec]

theorem resW_one {W : Submodule K (HypIndex 2 1 → K)} (hW : ∀ w ∈ W, (1 : GL (HypIndex 2 1) K) *ᵥ w ∈ W) :
    resW (1 : GL (HypIndex 2 1) K) hW = 1 := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  rw [resW_apply, Module.End.one_apply, Units.val_one, Matrix.one_mulVec]

theorem card_GL_two_four (hK : Nat.card K = 4) : Nat.card (GL (Fin 2) K) = 180 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  rw [Matrix.card_GL_field]
  simp [hcard, Fin.prod_univ_two]

@[expose] noncomputable def restrMat {h : UnitaryFieldData 2 1 K} {W : Submodule K (HypIndex 2 1 → K)}
    (b : Module.Basis (Fin 2) K W) (X : Subgroup (hypSU h 2 1)) (hX : X ≤ isoStabilizer h 2 1 W)
    (x : X) : Matrix (Fin 2) (Fin 2) K :=
  LinearMap.toMatrix b b (resW ((x : hypSU h 2 1) : GL (HypIndex 2 1) K)
    (fun w hw => mulVec_mem_of_isoStab (hX x.2) hw))

theorem restrMat_mul {h : UnitaryFieldData 2 1 K} {W : Submodule K (HypIndex 2 1 → K)}
    (b : Module.Basis (Fin 2) K W) (X : Subgroup (hypSU h 2 1)) (hX : X ≤ isoStabilizer h 2 1 W)
    (x y : X) : restrMat b X hX (x * y) = restrMat b X hX x * restrMat b X hX y := by
  unfold restrMat
  rw [← LinearMap.toMatrix_mul]
  congr 1
  exact resW_mul _ _ _

theorem restrMat_one {h : UnitaryFieldData 2 1 K} {W : Submodule K (HypIndex 2 1 → K)}
    (b : Module.Basis (Fin 2) K W) (X : Subgroup (hypSU h 2 1)) (hX : X ≤ isoStabilizer h 2 1 W) :
    restrMat b X hX 1 = 1 := by
  have hW1 : ∀ w ∈ W, (1 : GL (HypIndex 2 1) K) *ᵥ w ∈ W := fun w hw => by simpa using hw
  have h1 : resW (1 : GL (HypIndex 2 1) K) hW1 = 1 := resW_one hW1
  unfold restrMat
  show LinearMap.toMatrix b b (resW (1 : GL (HypIndex 2 1) K) hW1) = 1
  rw [h1, Module.End.one_eq_id, LinearMap.toMatrix_id]

@[expose] noncomputable def restrHom {h : UnitaryFieldData 2 1 K} {W : Submodule K (HypIndex 2 1 → K)}
    (b : Module.Basis (Fin 2) K W) (X : Subgroup (hypSU h 2 1)) (hX : X ≤ isoStabilizer h 2 1 W) :
    X →* GL (Fin 2) K where
  toFun x := Units.mk (restrMat b X hX x) (restrMat b X hX x⁻¹)
    (by rw [← restrMat_mul, mul_inv_cancel, restrMat_one])
    (by rw [← restrMat_mul, inv_mul_cancel, restrMat_one])
  map_one' := Units.ext (restrMat_one b X hX)
  map_mul' x y := Units.ext (restrMat_mul b X hX x y)

theorem restrHom_apply {h : UnitaryFieldData 2 1 K} {W : Submodule K (HypIndex 2 1 → K)}
    (b : Module.Basis (Fin 2) K W) (X : Subgroup (hypSU h 2 1)) (hX : X ≤ isoStabilizer h 2 1 W)
    (x : X) : ((restrHom b X hX x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = restrMat b X hX x :=
  rfl

theorem fixesPt_of_restrHom_eq_one {h : UnitaryFieldData 2 1 K} {W : Submodule K (HypIndex 2 1 → K)}
    (b : Module.Basis (Fin 2) K W) (X : Subgroup (hypSU h 2 1)) (hX : X ≤ isoStabilizer h 2 1 W)
    (x : X) (hx : restrHom b X hX x = 1) :
    FixesPt W ((x : hypSU h 2 1) : GL (HypIndex 2 1) K) := by
  unfold FixesPt
  have hm : restrMat b X hX x = 1 := by
    have := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) hx
    simpa [restrHom_apply] using this
  have hr : resW ((x : hypSU h 2 1) : GL (HypIndex 2 1) K)
      (fun w hw => mulVec_mem_of_isoStab (hX x.2) hw) = 1 := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_one]
    exact hm
  intro w hw
  have := congrArg (fun f : W →ₗ[K] W => ((f ⟨w, hw⟩ : W) : HypIndex 2 1 → K)) hr
  simpa [resW_apply] using this

theorem no_surj_two (hK : Nat.card K = 4) {h : UnitaryFieldData 2 1 K}
    {W : Submodule K (HypIndex 2 1 → K)} (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 1 x y = 0)
    (hk : Module.finrank K W = 2) (X : Subgroup (hypSU h 2 1)) (hX : X ≤ isoStabilizer h 2 1 W)
    (T : Type) [Group T] [Finite T] [IsSimpleGroup T] (hT : Nat.card T = 360) :
    ¬ ∃ φ : X →* T, Function.Surjective φ := by
  rintro ⟨φ, hφ⟩
  obtain ⟨F⟩ := exists_frame h W hW hk
  let b : Module.Basis (Fin 2) K W := Module.finBasisOfFinrankEq K W hk
  set ψ := restrHom b X hX with hψ
  have hYn : (ψ.ker.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  haveI := hYn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ψ.ker.map φ) with hbot | htop
  · have hle : ψ.ker ≤ φ.ker := by
      intro y hy
      have hmem : φ y ∈ ψ.ker.map φ := Subgroup.mem_map_of_mem φ hy
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    have h1 : φ.ker.index ∣ ψ.ker.index := Subgroup.index_dvd_of_le hle
    rw [Subgroup.index_ker φ, Subgroup.index_ker ψ] at h1
    have hφr : φ.range = ⊤ := MonoidHom.range_eq_top.mpr hφ
    rw [hφr, Subgroup.card_top, hT] at h1
    have hψd : Nat.card ψ.range ∣ Nat.card (GL (Fin 2) K) := Subgroup.card_subgroup_dvd_card _
    rw [card_GL_two_four hK] at hψd
    have h360 := h1.trans hψd
    norm_num at h360
  · set Yh : Subgroup (hypSU h 2 1) := ψ.ker.map X.subtype with hYh
    have hYfix : ∀ y ∈ Yh, FixesPt W ((y : hypSU h 2 1) : GL (HypIndex 2 1) K) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact fixesPt_of_restrHom_eq_one b X hX x (MonoidHom.mem_ker.mp hx)
    have hcardY : Nat.card Yh = Nat.card ψ.ker :=
      Subgroup.card_map_of_injective (Subtype.val_injective)
    have hd : Nat.card (ψ.ker.map φ) ∣ Nat.card ψ.ker := Subgroup.card_map_dvd _ φ
    rw [htop, Subgroup.card_top, hT] at hd
    have h5 : 5 ∣ Nat.card Yh := by
      rw [hcardY]
      exact (by norm_num : (5 : ℕ) ∣ 360).trans hd
    exact not_five_dvd_pointwise hK F Yh hYfix h5

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5

end
