module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelV0

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Matrix

def frobSL (g : SL2) : SL2 :=
  ⟨(g : Matrix (Fin 2) (Fin 2) F4).map F4.frob, by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]⟩

theorem coe_frobSL (g : SL2) :
    ((frobSL g : SL2) : Matrix (Fin 2) (Fin 2) F4) =
      (g : Matrix (Fin 2) (Fin 2) F4).map F4.frob := rfl

def thetaB0 (g : SL2 × SL2) : SL2 × SL2 := (frobSL g.2, frobSL g.1)

theorem b0Fun_actFun (g : SL2 × SL2) (M : V0) :
    b0Fun (actFun g M) = actFun (thetaB0 g) (b0Fun M) := by
  simp only [b0Fun, frobFun, actFun, thetaB0, coe_frobSL, Matrix.map_mul, Matrix.transpose_mul,
    Matrix.transpose_map, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem frobSL_mul (g h : SL2) : frobSL (g * h) = frobSL g * frobSL h := by
  apply Subtype.ext
  simp only [coe_frobSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]

theorem frobSL_one : frobSL 1 = 1 := by
  apply Subtype.ext
  simp only [coe_frobSL, Matrix.SpecialLinearGroup.coe_one, Matrix.map_one, map_zero, map_one]

theorem frobSL_frobSL (g : SL2) : frobSL (frobSL g) = g := by
  apply Subtype.ext
  refine Matrix.ext fun i j => ?_
  simp only [coe_frobSL, Matrix.map_apply]
  exact frob_frob _

def thetaEquiv : SL2 × SL2 ≃* SL2 × SL2 where
  toFun := thetaB0
  invFun := thetaB0
  left_inv g := by simp only [thetaB0, frobSL_frobSL]
  right_inv g := by simp only [thetaB0, frobSL_frobSL]
  map_mul' g h := by
    simp only [thetaB0, Prod.fst_mul, Prod.snd_mul, frobSL_mul, Prod.mk_mul_mk]

end CFSG.EvenSporadicStandard.HNRecog.CSide
