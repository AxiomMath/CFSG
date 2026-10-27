module

import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmQ8Eng182
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscSteps182
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen69
public import CFSG.ClassicalInvolution.AschTight.Sec6GenCyc66
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmE

section E182

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem mem_dstarComp_of_mem_USet_le_W [Finite G] (hΩ : HypOmegaGen Ω) {K J W V₀ V₁ : Subgroup G} (hK
    : K ∈ Ω) (hJ : J ∈ Ω)
    (hV₀ : V₀ ∈ USet Ω) (hV₀K : V₀ ≤ K) (hV₀W : V₀ ≤ W) (hV₁ : V₁ ∈ USet Ω) (hV₁J : V₁ ≤ J)
    (hV₁W : V₁ ≤ W) (habel : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : J ∈ dstarComp Ω K := by
  exact CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.MinCexQ8Frame.mem_dstarComp_of_mem_USet_le_W hΩ hK hJ hV₀ hV₀K hV₀W hV₁ hV₁J hV₁W habel

theorem etaAbelian_of_gen [Finite G] (hΩ : HypOmegaGen Ω) : EtaAbelian Ω :=
  fun S _ hη hinv => (Sec6Gen.eta_abelian_of_cyc66 hΩ (Sec6Gen.cyc66 hΩ) hη hinv).1

end E182

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
