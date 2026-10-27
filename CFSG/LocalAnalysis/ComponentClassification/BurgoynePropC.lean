module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOMain
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCExc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCU
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCSp

public section

namespace CFSG.ComponentClassification.Burgoyne

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.TBLit CFSG.Assembly.LowTwoRank


theorem burgoynePropC_of_input (hE3 : BurgoyneExcPropCInput) : BurgoynePropC := by
  intro X _ _ hX r hr R₁ R₂ hR₁ hR₁c hR₂ hR₂c p n _ hp2 hn hiso₁ hiso₂ hmem
  have hC : C.PropCData r R₁ R₂ p n := ⟨hp2, hn, hr, hR₁, hR₁c, hR₂, hR₂c, hiso₁, hiso₂, hmem⟩
  obtain ⟨τ, m, p', f', -, hp2', hadm, hL⟩ := hX.2.2.1
  cases τ with
  | POmegaOdd => exact C.burgoynePropC_POmegaOdd hX hp2' hL hC
  | PSL => exact (C.burgoynePropC_PSL hX hp2' hL hC).elim
  | PSU => exact (C.burgoynePropC_PSU hX hp2' hL hC).elim
  | PSp => exact (C.burgoynePropC_PSp hX hp2' hL hC).elim
  | POmegaMinus => exact (C.burgoynePropC_POmegaMinus hX hp2' hL hC).elim
  | POmegaPlus => exact (C.burgoynePropC_POmegaPlus hX hp2' hL hC).elim
  | G2 => exact (C.burgoynePropC_exceptional hE3 hX (by decide) hp2' hL hC).elim
  | F4 => exact (C.burgoynePropC_exceptional hE3 hX (by decide) hp2' hL hC).elim
  | E6 => exact (C.burgoynePropC_exceptional hE3 hX (by decide) hp2' hL hC).elim
  | E7 => exact (C.burgoynePropC_exceptional hE3 hX (by decide) hp2' hL hC).elim
  | E8 => exact (C.burgoynePropC_exceptional hE3 hX (by decide) hp2' hL hC).elim
  | twistedE6 => exact (C.burgoynePropC_exceptional hE3 hX (by decide) hp2' hL hC).elim
  | trialityD4 => exact (C.burgoynePropC_exceptional hE3 hX (by decide) hp2' hL hC).elim
  | twistedG2 => exact (C.burgoynePropC_exceptional hE3 hX (by decide) hp2' hL hC).elim
  | twistedB2 => exact absurd hadm.2.2.2.1 hp2'
  | twistedF4 => exact absurd hadm.2.2.2.1 hp2'
  | Tits => exact absurd hadm.2.2.2.1 hp2'

end CFSG.ComponentClassification.Burgoyne
