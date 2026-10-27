module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {F : Type} [Field F]

@[expose] def l3tVec (c : Fˣ) : Fin 3 → F := ![(c : F), ((c⁻¹ : Fˣ) : F), 1]

theorem l3tVec_mul (c d : Fˣ) (i : Fin 3) :
    l3tVec (F := F) (c * d) i = l3tVec c i * l3tVec d i := by
  fin_cases i <;> simp [l3tVec, mul_comm]

theorem det_l3tVec (c : Fˣ) : (Matrix.diagonal (l3tVec (F := F) c)).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp [l3tVec]

@[expose] noncomputable def diagL3 (c : Fˣ) : SpecialLinearGroup (Fin 3) F :=
  ⟨Matrix.diagonal (l3tVec c), det_l3tVec c⟩

theorem coe_diagL3 (c : Fˣ) :
    ((diagL3 c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal (l3tVec c) := rfl

@[expose] noncomputable def l3tDiag : Fˣ →* SpecialLinearGroup (Fin 3) F where
  toFun := diagL3
  map_one' := by
    ext i j
    rw [coe_diagL3]
    fin_cases i <;> fin_cases j <;> simp [l3tVec]
  map_mul' c d := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagL3, coe_diagL3, coe_diagL3,
      Matrix.diagonal_mul_diagonal]
    rw [funext (l3tVec_mul c d)]

theorem coe_l3tDiag (c : Fˣ) :
    ((l3tDiag c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal (l3tVec c) := rfl

@[expose] noncomputable def l3Tor : Fˣ →* projectiveSL 3 F := (proj 3 F).comp l3tDiag

theorem l3Tor_injective : Function.Injective (l3Tor (F := F)) := by
  intro a b hab
  have h1 : (l3tDiag a)⁻¹ * l3tDiag b ∈ scalars 3 F := by
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv]
    have : proj 3 F (l3tDiag a) = proj 3 F (l3tDiag b) := hab
    rw [this, inv_mul_cancel]
  rw [← map_inv, ← map_mul, mem_scalars] at h1
  obtain ⟨c, -, hc⟩ := h1
  have e2 := congrFun (congrFun hc 2) 2
  have e0 := congrFun (congrFun hc 0) 0
  simp only [coe_l3tDiag, Matrix.diagonal_apply_eq, Matrix.scalar_apply] at e2 e0
  simp only [l3tVec, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons] at e2 e0
  have hc1 : (c : F) = 1 := e2.symm
  have hab1 : ((a⁻¹ * b : Fˣ) : F) = 1 := e0.trans hc1
  exact inv_mul_eq_one.mp (Units.ext hab1)

theorem map_l3tDiag (σ : F ≃+* F) (c : Fˣ) :
    SpecialLinearGroup.map σ.toRingHom (l3tDiag c) = l3tDiag (Units.map (σ : F →* F) c) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_l3tDiag, coe_l3tDiag]
  fin_cases i <;> fin_cases j <;>
    simp [l3tVec, Matrix.map_apply]

theorem fieldAut_l3Tor (σ : F ≃+* F) (c : Fˣ) :
    fieldAut 3 F σ (l3Tor c) = l3Tor (Units.map (σ : F →* F) c) := by
  rw [l3Tor, MonoidHom.comp_apply, fieldAut_proj, map_l3tDiag]
  rfl

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
