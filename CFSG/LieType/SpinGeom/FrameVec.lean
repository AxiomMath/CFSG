module

public import CFSG.LieType.SpinGeom.Mem

public section

namespace CFSG.LieType.SpinGeom

open scoped Matrix

section FrameVecAlgebra

variable {K : Type} [Field K]

theorem xvec_frameVec (x₀ : K) (x y : Fin 3 → K) (y₀ : K) :
    xvec K (frameVec K x₀ x y y₀) = x :=
  funext fun j => coordX_frameVec_succ x₀ x y y₀ j

theorem yvec_frameVec (x₀ : K) (x y : Fin 3 → K) (y₀ : K) :
    yvec K (frameVec K x₀ x y y₀) = y :=
  funext fun j => coordY_frameVec_succ x₀ x y y₀ j

theorem frameVec_inj {x₀ x₀' y₀ y₀' : K} {x x' y y' : Fin 3 → K}
    (h : frameVec K x₀ x y y₀ = frameVec K x₀' x' y' y₀') :
    x₀ = x₀' ∧ x = x' ∧ y = y' ∧ y₀ = y₀' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [coordX_frameVec_zero] using congrArg (fun v => coordX K v 0) h
  · simpa [xvec_frameVec] using congrArg (xvec K) h
  · simpa [yvec_frameVec] using congrArg (yvec K) h
  · simpa [coordY_frameVec_zero] using congrArg (fun v => coordY K v 0) h

theorem frameVec_add (x₀ x₀' : K) (x x' y y' : Fin 3 → K) (y₀ y₀' : K) :
    frameVec K x₀ x y y₀ + frameVec K x₀' x' y' y₀' =
      frameVec K (x₀ + x₀') (x + x') (y + y') (y₀ + y₀') := by
  apply vec_ext
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordX_add, coordX_frameVec_zero, coordX_frameVec_zero, coordX_frameVec_zero]
    · rw [coordX_add, coordX_frameVec_succ, coordX_frameVec_succ, coordX_frameVec_succ]
      rfl
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordY_add, coordY_frameVec_zero, coordY_frameVec_zero, coordY_frameVec_zero]
    · rw [coordY_add, coordY_frameVec_succ, coordY_frameVec_succ, coordY_frameVec_succ]
      rfl

theorem frameVec_smul (r x₀ y₀ : K) (x y : Fin 3 → K) :
    r • frameVec K x₀ x y y₀ = frameVec K (r * x₀) (r • x) (r • y) (r * y₀) := by
  apply vec_ext
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordX_smul, coordX_frameVec_zero, coordX_frameVec_zero]
    · rw [coordX_smul, coordX_frameVec_succ, coordX_frameVec_succ]
      rfl
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordY_smul, coordY_frameVec_zero, coordY_frameVec_zero]
    · rw [coordY_smul, coordY_frameVec_succ, coordY_frameVec_succ]
      rfl

theorem frameVec_zero : frameVec K 0 0 0 0 = 0 := by
  apply vec_ext
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordX_frameVec_zero, coordX_zero]
    · rw [coordX_frameVec_succ, coordX_zero]
      rfl
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordY_frameVec_zero, coordY_zero]
    · rw [coordY_frameVec_succ, coordY_zero]
      rfl

theorem frameE_zero_eq : frameE K 0 = frameVec K 1 0 0 0 := by
  apply vec_ext
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordX_frameVec_zero, coordX_frameE, if_pos rfl]
    · rw [coordX_frameVec_succ, coordX_frameE, if_neg (Fin.succ_ne_zero l).symm]
      rfl
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordY_frameVec_zero, coordY_frameE]
    · rw [coordY_frameVec_succ, coordY_frameE]
      rfl

end FrameVecAlgebra

section ActionOnFrameVec

variable {K : Type} [Field K]

theorem spinElt_frameVec (c m : Fin 3 → K) (g : Matrix (Fin 3) (Fin 3) K) (x₀ : K)
    (x y : Fin 3 → K) (y₀ : K) :
    spinElt K c m g (frameVec K x₀ x y y₀) =
      frameVec K (x₀ + c ⬝ᵥ (g *ᵥ x) + m ⬝ᵥ ((g.adjugate)ᵀ *ᵥ y) + y₀ * (c ⬝ᵥ m))
        (g *ᵥ x + y₀ • m) ((g.adjugate)ᵀ *ᵥ y + altMat K m *ᵥ (g *ᵥ x) + y₀ • c) y₀ := by
  apply vec_ext
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordX_spinElt_zero, coordX_frameVec_zero, xvec_frameVec, yvec_frameVec,
        coordY_frameVec_zero, coordX_frameVec_zero]
    · rw [coordX_spinElt_succ, coordX_frameVec_succ, xvec_frameVec, coordY_frameVec_zero]
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordY_spinElt_zero, coordY_frameVec_zero, coordY_frameVec_zero]
    · rw [coordY_spinElt_succ, coordY_frameVec_succ, xvec_frameVec, yvec_frameVec,
        coordY_frameVec_zero]

theorem spinElt_iota_frameVec (g : Matrix (Fin 3) (Fin 3) K) (x₀ : K) (x y : Fin 3 → K)
    (y₀ : K) :
    spinElt K 0 0 g (frameVec K x₀ x y y₀) =
      frameVec K x₀ (g *ᵥ x) ((g.adjugate)ᵀ *ᵥ y) y₀ := by
  rw [spinElt_frameVec]
  simp [altMat_zero]

theorem spinElt_zeta_frameVec (m : Fin 3 → K) (x₀ : K) (x y : Fin 3 → K) (y₀ : K) :
    spinElt K 0 m 1 (frameVec K x₀ x y y₀) =
      frameVec K (x₀ + m ⬝ᵥ y) (x + y₀ • m) (y + altMat K m *ᵥ x) y₀ := by
  rw [spinElt_frameVec]
  simp

end ActionOnFrameVec

end CFSG.LieType.SpinGeom
