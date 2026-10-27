module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamLie

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

theorem gapFinalPumpup_of_families (hS : ∀ name, GapFinalPumpupSpor name)
    (hL : GapFinalPumpupLie) : GapFinalPumpup := by
  intro Y _ _ hq hK hcore x hxo J₁ hJ₁ hty
  obtain ⟨hnab, i, ⟨e⟩⟩ := I1420.catalog_of_quasisimple hq hK
  cases i with
  | cyclic q hq' =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exact gapFinalPumpupAlt_holds Y hq hK hcore ⟨n, hn, ⟨e⟩⟩ x hxo J₁ hJ₁ hty
  | lie idx => exact hL Y hq hK hcore ⟨idx, ⟨e⟩⟩ x hxo J₁ hJ₁ hty
  | sporadic name => exact hS name Y hq hK hcore ⟨e⟩ x hxo J₁ hJ₁ hty

theorem gapFinalPumpup_of_residuals
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hOG : UniquenessMaximal.InputONGroup)
    (hR : ∀ name ∈ sporResidualNames, SporNoPumpup name) (hON : ONSimpleNoPumpup)
    (hb : LieOrderBridge) (h1 : LieDownChev) (h2 : LieNoHatSix) : GapFinalPumpup :=
  gapFinalPumpup_of_families (gapFinalPumpupSpor_of_residuals hSpM hOrd hOG hR hON)
    (gapFinalPumpupLie_of_residuals hb hOG h1 h2)

end CFSG.HardMathSupport.Solomon.Coordinator
