module

public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec128_lieModelPSU34_dvd13 {E : Type} [Group E] (h : LieModel E .PSU 3 2 2) :
    13 ∣ Nat.card E := by
  have hc := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by decide) h
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hc).2.1 rfl]
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
