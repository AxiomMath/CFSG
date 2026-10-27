module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherParabolicData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Open
open scoped Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def FixesPt (W : Submodule K (HypIndex 2 0 → K)) (g : GL (HypIndex 2 0) K) : Prop :=
  ∀ w ∈ W, (g : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w = w


theorem mulVec_mem_of_isoStab {h : UnitaryFieldData 2 3 K} {W : Submodule K (HypIndex 2 0 → K)}
    {g : hypSU h 2 0} (hg : g ∈ isoStabilizer h 2 0 W) {w : HypIndex 2 0 → K} (hw : w ∈ W) :
    ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W := by
  have hs : g • W = W := MulAction.mem_stabilizer_iff.mp hg
  have hs' : (g : GL (HypIndex 2 0) K) • W = W := hs
  have hmem : ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈
      (g : GL (HypIndex 2 0) K) • W := by
    rw [smul_eq_map]
    exact ⟨w, hw, rfl⟩
  rwa [hs'] at hmem

@[expose] noncomputable def resW {W : Submodule K (HypIndex 2 0 → K)} (x : GL (HypIndex 2 0) K)
    (hx : ∀ w ∈ W, (x : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W) : W →ₗ[K] W :=
  LinearMap.restrict (Matrix.mulVecLin (x : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) hx

theorem resW_apply {W : Submodule K (HypIndex 2 0 → K)} (x : GL (HypIndex 2 0) K)
    (hx : ∀ w ∈ W, (x : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W) (w : W) :
    ((resW x hx w : W) : HypIndex 2 0 → K) = (x : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ (w : HypIndex 2 0 → K) :=
  rfl

theorem resW_mul {W : Submodule K (HypIndex 2 0 → K)} {x y : GL (HypIndex 2 0) K}
    (hx : ∀ w ∈ W, (x : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W)
    (hy : ∀ w ∈ W, (y : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W)
    (hxy : ∀ w ∈ W, ((x * y : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W) :
    resW (x * y) hxy = resW x hx * resW y hy := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  rw [Module.End.mul_apply, resW_apply, resW_apply, resW_apply, Units.val_mul,
    Matrix.mulVec_mulVec]

theorem resW_one {W : Submodule K (HypIndex 2 0 → K)} (hW : ∀ w ∈ W, (1 : GL (HypIndex 2 0) K) *ᵥ w ∈ W) :
    resW (1 : GL (HypIndex 2 0) K) hW = 1 := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  rw [resW_apply, Module.End.one_apply, Units.val_one, Matrix.one_mulVec]

@[expose] noncomputable def restrMat {h : UnitaryFieldData 2 3 K} {W : Submodule K (HypIndex 2 0 → K)}
    (b : Module.Basis (Fin 2) K W) (X : Subgroup (hypSU h 2 0)) (hX : X ≤ isoStabilizer h 2 0 W)
    (x : X) : Matrix (Fin 2) (Fin 2) K :=
  LinearMap.toMatrix b b (resW ((x : hypSU h 2 0) : GL (HypIndex 2 0) K)
    (fun w hw => mulVec_mem_of_isoStab (hX x.2) hw))

theorem restrMat_mul {h : UnitaryFieldData 2 3 K} {W : Submodule K (HypIndex 2 0 → K)}
    (b : Module.Basis (Fin 2) K W) (X : Subgroup (hypSU h 2 0)) (hX : X ≤ isoStabilizer h 2 0 W)
    (x y : X) : restrMat b X hX (x * y) = restrMat b X hX x * restrMat b X hX y := by
  unfold restrMat
  rw [← LinearMap.toMatrix_mul]
  congr 1
  exact resW_mul _ _ _

theorem restrMat_one {h : UnitaryFieldData 2 3 K} {W : Submodule K (HypIndex 2 0 → K)}
    (b : Module.Basis (Fin 2) K W) (X : Subgroup (hypSU h 2 0)) (hX : X ≤ isoStabilizer h 2 0 W) :
    restrMat b X hX 1 = 1 := by
  have hW1 : ∀ w ∈ W, (1 : GL (HypIndex 2 0) K) *ᵥ w ∈ W := fun w hw => by simpa using hw
  have h1 : resW (1 : GL (HypIndex 2 0) K) hW1 = 1 := resW_one hW1
  unfold restrMat
  show LinearMap.toMatrix b b (resW (1 : GL (HypIndex 2 0) K) hW1) = 1
  rw [h1, Module.End.one_eq_id, LinearMap.toMatrix_id]

@[expose] noncomputable def restrHom {h : UnitaryFieldData 2 3 K} {W : Submodule K (HypIndex 2 0 → K)}
    (b : Module.Basis (Fin 2) K W) (X : Subgroup (hypSU h 2 0)) (hX : X ≤ isoStabilizer h 2 0 W) :
    X →* GL (Fin 2) K where
  toFun x := Units.mk (restrMat b X hX x) (restrMat b X hX x⁻¹)
    (by rw [← restrMat_mul, mul_inv_cancel, restrMat_one])
    (by rw [← restrMat_mul, inv_mul_cancel, restrMat_one])
  map_one' := Units.ext (restrMat_one b X hX)
  map_mul' x y := Units.ext (restrMat_mul b X hX x y)

theorem restrHom_apply {h : UnitaryFieldData 2 3 K} {W : Submodule K (HypIndex 2 0 → K)}
    (b : Module.Basis (Fin 2) K W) (X : Subgroup (hypSU h 2 0)) (hX : X ≤ isoStabilizer h 2 0 W)
    (x : X) : ((restrHom b X hX x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = restrMat b X hX x :=
  rfl

theorem fixesPt_of_restrHom_eq_one {h : UnitaryFieldData 2 3 K} {W : Submodule K (HypIndex 2 0 → K)}
    (b : Module.Basis (Fin 2) K W) (X : Subgroup (hypSU h 2 0)) (hX : X ≤ isoStabilizer h 2 0 W)
    (x : X) (hx : restrHom b X hX x = 1) :
    FixesPt W ((x : hypSU h 2 0) : GL (HypIndex 2 0) K) := by
  unfold FixesPt
  have hm : restrMat b X hX x = 1 := by
    have := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) hx
    simpa [restrHom_apply] using this
  have hr : resW ((x : hypSU h 2 0) : GL (HypIndex 2 0) K)
      (fun w hw => mulVec_mem_of_isoStab (hX x.2) hw) = 1 := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_one]
    exact hm
  intro w hw
  have := congrArg (fun f : W →ₗ[K] W => ((f ⟨w, hw⟩ : W) : HypIndex 2 0 → K)) hr
  simpa [resW_apply] using this

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4

end
