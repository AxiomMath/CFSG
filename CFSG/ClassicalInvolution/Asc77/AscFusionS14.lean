module

public import CFSG.ClassicalInvolution.Asc77.AscFusionS12
public import CFSG.ClassicalInvolution.Asc77.AscFusionS13
public import CFSG.ClassicalInvolution.Asc77.AscFusionR14

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime]


theorem bigOrderCyc (p f : ℕ) [Fact p.Prime] : BigOrderCyc p f := by
  intro G _ _ _ hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 h8 hvz hvK _
  by_contra hv
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have htK : t ∈ Subgroup.normalizer (K : Set G) := hH K (CoreAssembly.mem_conjClass_self K) hKz
  have hvK' : v * v ∈ Subgroup.normalizer (K : Set G) := by simpa [pow_two] using hvK
  exact big_order_contradiction hp2 hq hz hJ ht hne htK hvJ hv2 h8 hvz hvK' hv

theorem fusionCoreStmt (p f : ℕ) [Fact p.Prime] : FusionCoreStmt p f :=
  fusionCore_of_residuals_cyc p f (prop370 p f) (noQuasidihedral p f) (bigOrderCyc p f)

end CFSG.ClassicalInvolution.Asc77.AscFusion
