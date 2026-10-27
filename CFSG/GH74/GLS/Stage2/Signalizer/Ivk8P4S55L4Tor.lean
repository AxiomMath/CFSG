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

@[expose] def sl4Vec (c : Fˣ) : Fin 4 → F := ![(c : F), ((c⁻¹ : Fˣ) : F), 1, 1]

theorem sl4Vec_mul (c d : Fˣ) (i : Fin 4) :
    sl4Vec (F := F) (c * d) i = sl4Vec c i * sl4Vec d i := by
  fin_cases i <;> simp [sl4Vec, mul_comm]

theorem det_sl4Vec (c : Fˣ) : (Matrix.diagonal (sl4Vec (F := F) c)).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_four]
  simp [sl4Vec]

@[expose] noncomputable def diag4 (c : Fˣ) : SpecialLinearGroup (Fin 4) F :=
  ⟨Matrix.diagonal (sl4Vec c), det_sl4Vec c⟩

theorem coe_diag4 (c : Fˣ) :
    ((diag4 c : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal (sl4Vec c) := rfl

@[expose] noncomputable def sl4Diag : Fˣ →* SpecialLinearGroup (Fin 4) F where
  toFun := diag4
  map_one' := by
    ext i j
    rw [coe_diag4]
    fin_cases i <;> fin_cases j <;> simp [sl4Vec]
  map_mul' c d := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_diag4, coe_diag4, coe_diag4,
      Matrix.diagonal_mul_diagonal]
    rw [funext (sl4Vec_mul c d)]

theorem coe_sl4Diag (c : Fˣ) :
    ((sl4Diag c : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal (sl4Vec c) := rfl

@[expose] noncomputable def l4Tor : Fˣ →* projectiveSL 4 F := (proj 4 F).comp sl4Diag

theorem l4Tor_injective : Function.Injective (l4Tor (F := F)) := by
  intro a b hab
  have h1 : (sl4Diag a)⁻¹ * sl4Diag b ∈ scalars 4 F := by
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv]
    have : proj 4 F (sl4Diag a) = proj 4 F (sl4Diag b) := hab
    rw [this, inv_mul_cancel]
  rw [← map_inv, ← map_mul, mem_scalars] at h1
  obtain ⟨c, -, hc⟩ := h1
  have e2 := congrFun (congrFun hc 2) 2
  have e0 := congrFun (congrFun hc 0) 0
  simp only [coe_sl4Diag, Matrix.diagonal_apply_eq, Matrix.scalar_apply] at e2 e0
  simp only [sl4Vec, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons] at e2 e0
  have hc1 : (c : F) = 1 := e2.symm
  have hab1 : ((a⁻¹ * b : Fˣ) : F) = 1 := e0.trans hc1
  exact inv_mul_eq_one.mp (Units.ext hab1)

theorem map_sl4Diag (σ : F ≃+* F) (c : Fˣ) :
    SpecialLinearGroup.map σ.toRingHom (sl4Diag c) = sl4Diag (Units.map (σ : F →* F) c) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_sl4Diag, coe_sl4Diag]
  fin_cases i <;> fin_cases j <;>
    simp [sl4Vec, Matrix.map_apply]

theorem fieldAut_l4Tor (σ : F ≃+* F) (c : Fˣ) :
    fieldAut 4 F σ (l4Tor c) = l4Tor (Units.map (σ : F →* F) c) := by
  rw [l4Tor, MonoidHom.comp_apply, fieldAut_proj, map_sl4Diag]
  rfl

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
