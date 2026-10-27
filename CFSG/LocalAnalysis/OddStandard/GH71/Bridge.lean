module

public import CFSG.LocalAnalysis.OddStandard.GH71.Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P112CenU

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75


theorem oddCoreThreeLy_proved : Gap56.OddCoreThreeLy := by
  intro G _ _ z S hctx
  have e : Nat.card (OddCore z) = Nat.card (pPrimeCore 2 ↥(Cen z)) :=
    card_map_of_injective (Cen z).subtype_injective
  rw [e, oddCore_eq_bot_of_stage2_ly hctx, Subgroup.card_bot]
  norm_num

end CFSG.OddStandard.GH71
