module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCT3c
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCT4
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCShape

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Thin


theorem a7TCThin_proved : A7TCThin := by
  intro G _ _ _ Ω K hs hnt hedge _ th1 th2
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨J, hJ, -⟩ := a7C27_nbr_proved G Ω K hs hedge
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hs.mem
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ.1
  obtain ⟨S, R, T, W, h7⟩ := Hat2A7S8.T21.exists_std8A7 hs (hnt K hs.mem) hz hJ ht
  have hC : Hat2A7S8.Asc77.T8R.Core.Core26All Ω := fun K₁ J₁ S₁ R₁ T₁ W₁ z₁ t₁ hs₁ =>
    Hat2A7S8.T21.core26_of_thin hs₁ (th1 K₁ hs₁.stand.mem z₁ hs₁.hz) (th2 K₁ hs₁.stand.mem)
  exact Hat2A7S8.Asc77.T8R.Core.false_of_core26 (Hat2A7S8.Asc77.Std8.of_std8A7 h7) hC

end Thin

end CFSG.ClassicalInvolution.Hat2A7S
