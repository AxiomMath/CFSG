module

public import CFSG.ClassicalInvolution.Asc77.AscFusionS6
public import CFSG.ClassicalInvolution.Asc77.AscFusionS9

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ComponentClassification
open scoped commutatorElement


theorem diagCentral (p f : ℕ) [Fact p.Prime] : DiagCentral p f := by
  intro G _ _ _ hnab hp2 hq K₀ z₀ h₀ hbelow K hK z hKz J hJ t hJt hne hzt hzJ htK q hqK hq2 hcomm
  have hKne : K ≠ conjSub t K := fun h =>
    htK (AscHypOmega.mem_normalizer_of_conjSub_eq h.symm)
  exact diag_centralizes_of_bad hp2 hq h₀ hK hKz hJt.sq hzt.symm hKne hJ hJt hqK hq2 hcomm hzJ
    fun x hxJ hx4 hxz => htK (bstar hp2 hq h₀ hJ hK hJt hKz hxJ hx4 hxz.symm)

theorem prop370 (p f : ℕ) [Fact p.Prime] : Prop370 p f :=
  prop370_of_diagCentral p f (diagCentral p f)

end CFSG.ClassicalInvolution.Asc77.AscFusion
