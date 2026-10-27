module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmega
public import Certificates.Data.OmegaSevenMax.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega.E7RootSet

open Certificates.OmegaSevenMax TauCeti QuadraticMap CFSG.ClassicalInvolution
open scoped Matrix

@[expose] def Mq : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  !![1, 0, 2, 0, 0, 0, 0;
     0, 1, 0, 2, 0, 0, 0;
     0, 0, 1, 2, 0, 0, 0;
     0, 0, 0, 1, 2, 0, 0;
     0, 0, 0, 0, 1, 2, 0;
     0, 0, 0, 0, 0, 1, 2;
     0, 0, 0, 0, 0, 0, 1]

noncomputable def qForm : QuadraticForm (ZMod 3) V := Matrix.toQuadraticForm' Mq

theorem qForm_apply (x : V) : qForm x = qV x := by
  simp only [qForm, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']
  simp [Mq, qV, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private theorem polar_aux (x0 x1 x2 x3 x4 x5 x6 y0 y1 y2 y3 y4 y5 y6 : ZMod 3) :
    ((x0 + y0) * (x0 + y0) + (x1 + y1) * (x1 + y1) + (x2 + y2) * (x2 + y2) +
        (x3 + y3) * (x3 + y3) + (x4 + y4) * (x4 + y4) + (x5 + y5) * (x5 + y5) +
        (x6 + y6) * (x6 + y6) +
        2 * ((x0 + y0) * (x2 + y2) + (x1 + y1) * (x3 + y3) + (x2 + y2) * (x3 + y3) +
          (x3 + y3) * (x4 + y4) + (x4 + y4) * (x5 + y5) + (x5 + y5) * (x6 + y6))) -
      (x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3 + x4 * x4 + x5 * x5 + x6 * x6 +
        2 * (x0 * x2 + x1 * x3 + x2 * x3 + x3 * x4 + x4 * x5 + x5 * x6)) -
      (y0 * y0 + y1 * y1 + y2 * y2 + y3 * y3 + y4 * y4 + y5 * y5 + y6 * y6 +
        2 * (y0 * y2 + y1 * y3 + y2 * y3 + y3 * y4 + y4 * y5 + y5 * y6)) =
    2 * (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4 + x5 * y5 + x6 * y6) +
      2 * (x0 * y2 + x2 * y0 + x1 * y3 + x3 * y1 + x2 * y3 + x3 * y2 +
        x3 * y4 + x4 * y3 + x4 * y5 + x5 * y4 + x5 * y6 + x6 * y5) := by
  ring

theorem polar_qForm (x y : V) : QuadraticMap.polar qForm x y = polarV x y := by
  rw [QuadraticMap.polar, qForm_apply, qForm_apply, qForm_apply]
  exact polar_aux (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5)
    (y 6)

variable (hQ : qForm.Nondegenerate)

noncomputable def toEq (g : omegaGroup hQ) : V ≃ₗ[ZMod 3] V :=
  ((g : OGroup qForm) : V ≃ₗ[ZMod 3] V)

theorem toEq_eq_coe (g : omegaGroup hQ) :
    toEq hQ g = ((g : OGroup qForm) : V ≃ₗ[ZMod 3] V) := by
  simp [toEq]

theorem toEq_one (x : V) : toEq hQ 1 x = x := by
  first | rfl | simp [toEq]

theorem toEq_mul (g h : omegaGroup hQ) (x : V) : toEq hQ (g * h) x = toEq hQ g (toEq hQ h x) := by
  first | rfl | simp [toEq]

noncomputable instance instMulActionFinset : MulAction (omegaGroup hQ) (Finset V) where
  smul g S := S.image (toEq hQ g)
  one_smul S := by
    show S.image (toEq hQ 1) = S
    ext x
    simp [toEq_one]
  mul_smul g h S := by
    show S.image (toEq hQ (g * h)) = (S.image (toEq hQ h)).image (toEq hQ g)
    rw [Finset.image_image]
    exact Finset.image_congr (fun x _ => toEq_mul hQ g h x)

theorem smul_def (g : omegaGroup hQ) (S : Finset V) : g • S = S.image (toEq hQ g) := rfl

set_option warn.classDefReducibility false in
def invQ (u : V) (hu : qV u = 1) : Invertible (qForm u) :=
  ⟨1, by simp [qForm_apply, hu], by simp [qForm_apply, hu]⟩

noncomputable def reflEl (u : V) (hu : qV u = 1) : OGroup qForm :=
  @TauCeti.QuadraticMap.reflectionOrthogonal (ZMod 3) V _ _ _ qForm u (invQ u hu)

theorem reflEl_apply (u : V) (hu : qV u = 1) (x : V) :
    ((reflEl u hu : OGroup qForm) : V ≃ₗ[ZMod 3] V) x = rxV u x := by
  unfold reflEl
  rw [@TauCeti.QuadraticMap.coe_reflectionOrthogonal (ZMod 3) V _ _ _ qForm u (invQ u hu),
    @TauCeti.QuadraticMap.reflection_apply (ZMod 3) V _ _ _ qForm u (invQ u hu), polar_qForm]
  show x - ((1 : ZMod 3) * polarV u x) • u = x - polarV u x • u
  rw [one_mul]

theorem detSpinorNorm_reflEl (u : V) (hu : qV u = 1) :
    detSpinorNorm hQ (reflEl u hu) =
      ((-1 : (ZMod 3)ˣ), (1 : Multiplicative (SquareClassGroup (ZMod 3)))) := by
  let _ : Invertible (qForm u) := invQ u hu
  have hunit : unitOfInvertible (qForm u) = (1 : (ZMod 3)ˣ) :=
    Units.ext (by rw [val_unitOfInvertible, qForm_apply, hu]; rfl)
  have h := detSpinorNorm_reflectionOrthogonal hQ u
  rw [hunit, map_one] at h
  exact h

theorem refl_mul_mem (u w : V) (hu : qV u = 1) (hw : qV w = 1) :
    reflEl u hu * reflEl w hw ∈ omegaGroup hQ := by
  rw [mem_omegaGroup_iff hQ, map_mul, detSpinorNorm_reflEl hQ u hu, detSpinorNorm_reflEl hQ w hw]
  refine Prod.ext ?_ ?_
  · show (-1 : (ZMod 3)ˣ) * -1 = 1
    first | decide | simp
  · show (1 : Multiplicative (SquareClassGroup (ZMod 3))) * 1 = 1
    exact mul_one 1

noncomputable def omegaEl (u w : V) (hu : qV u = 1) (hw : qV w = 1) : omegaGroup hQ :=
  ⟨reflEl u hu * reflEl w hw, refl_mul_mem hQ u w hu hw⟩

theorem toEq_omegaEl (u w : V) (hu : qV u = 1) (hw : qV w = 1) (x : V) :
    toEq hQ (omegaEl hQ u w hu hw) x = rxV u (rxV w x) := by
  show (reflEl u hu : V ≃ₗ[ZMod 3] V) ((reflEl w hw : V ≃ₗ[ZMod 3] V) x) = rxV u (rxV w x)
  rw [reflEl_apply u hu, reflEl_apply w hw]

theorem omegaEl_smul (u w : V) (hu : qV u = 1) (hw : qV w = 1) (S : Finset V) :
    omegaEl hQ u w hu hw • S = S.image (fun x => rxV u (rxV w x)) := by
  rw [smul_def]
  exact Finset.image_congr (fun x _ => toEq_omegaEl hQ u w hu hw x)

end CFSG.OddStandard.SmallF3.Omega.E7RootSet

end
