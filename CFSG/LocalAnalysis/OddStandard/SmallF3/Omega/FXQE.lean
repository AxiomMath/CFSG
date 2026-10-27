module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXQECenter
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXQEIsI4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXQEIndex
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FA8FinD
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L511Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82FactQCentExp6_of (hS : Asc82SchurU43) : Asc82FactQCentExp6 := by
  intro G _ _ L z hL Q₁ Q₂ hQ₁ hQ₂ h₁ h₂ hc hcard hz hzc x hxN hxC
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  obtain ⟨hzz, hz1, hz₁, hz₂, he₁, he₂⟩ := fx_qe_center_data e₁ e₂ hc hz
  have hI4 : IsI4PlusIn L z := fx_qe_isI4PlusIn hS hL hQ₁ hQ₂ e₁ e₂ hc hz₁ hz₂ he₁ he₂ hzz hz1 hzc
  have hY := asc82FactQCentOrd6_of hS G L z hL hI4 Q₁ Q₂ hQ₁ hQ₂ ⟨e₁⟩ ⟨e₂⟩ hc hcard hz hzc
    (zpowers x) ((Subgroup.zpowers_le).mpr hxN) ((Subgroup.zpowers_le).mpr hxC)
  exact fx_qe_pow_four_mem hY.1 hY.2

end CFSG.OddStandard.SmallF3.Omega
