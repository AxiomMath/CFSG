module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneEigen
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLiftLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveFFactor

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial oddCoreLift HasBLift)

section Data

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem map_conj_map_conj_eq_of_mul_self {t : G} (ht : t * t = 1) (X : Subgroup G) :
    (X.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = X := by
  have hid : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id G := by
    ext y
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, MonoidHom.id_apply]
    calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
      _ = y := by rw [ht]; group
  rw [map_map, hid, map_id]

variable [Finite G]

end Data

end CFSG.SeitzReduction.LinearPilot
