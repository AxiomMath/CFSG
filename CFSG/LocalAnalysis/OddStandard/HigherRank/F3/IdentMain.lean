module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Thm2Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.IdentPump
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.IdentCore

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification CFSG.ComponentClassification.HarrisLit

theorem identGenInput_of (hP2 : GS82PumpInputs.ChevOddCentralPumpInput)
    (hP8 : GS82PumpInputs.SpFourThreeCentralPumpInput)
    (hGA : TBLit.GriessMultipliersAllModels) (hE7 : Ident.E7ThreeRow)
    (hO : CatLeaf.LieOrderFormulasInput) : IdentGenInput := by
  intro G _ _ _ hnonab hKP _ w v hw hv2 hvw hvM J hJ hJM hJs hwJ K _ hJK hKc hwK hKnot hKv
  have hKchev := Ident.isSimpleChevalleyOver_bar_of_pumpup hP2 hP8 hO hnonab hKP hw hv2 hvw
    hvM hJ hJs hwJ hJK hKc hwK hKv
  have hwc : (⟨w, hwK⟩ : ↥K) ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have h := Subgroup.mem_centralizer_iff.mp (hKc.1 k.2) w (Set.mem_singleton w)
    exact h.symm
  have hw' : orderOf (⟨w, hwK⟩ : ↥K) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hw
  have e := (Subgroup.subgroupOfEquivOfLe hJK).symm
  exact Ident.false_of_pumped hGA hE7 hKc.2.2 hKchev hKnot hw' hwc
    (isTwoQuasisimple_of_mulEquiv e hJ.2.2) (T23.isMTypeSchur_of_mulEquiv e hJM)
    (ClassBShape.of_mulEquiv e hJs) (Subgroup.mem_subgroupOf.mpr hwJ)

end CFSG.OddStandard.HigherRank.F3
