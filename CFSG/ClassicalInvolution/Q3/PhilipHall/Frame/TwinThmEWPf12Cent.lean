module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf2Base
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf4Six
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf12Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWHull

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Cent
variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem normal_two_central_Q8 (hΩ : HypOmegaGen Ω) (hcls : Q3CL.ClassicalClause Ω)
    (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) {Q : Subgroup G} [Q.Normal]
    (hQ2 : IsPGroup 2 ↥Q) {J : Subgroup G} (hJ : J ∈ Ω) (hJQ : J ⊓ Q = ⊥) :
    J ≤ Subgroup.centralizer (Q : Set G) :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.normal_two_central_Q8 hΩ hcls h2 hQ2 hJ hJQ

@[expose] def E18_6NotO2Q8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H →
      ∀ z : G, IsUniqueInvolution K z → ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 ↥Q → z ∉ Q

theorem e18_6O2Q8_of (h5 : E18_5Q8) (hN : E18_6NotO2Q8) : E18_6O2Q8 := by
  intro G _ _ Ω K S R W H c Q hQn hQ2
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := e18_3Q8 G Ω K S R W H c
  have hgen : (⨆ J ∈ Ω, J) = ⊤ := h5 G Ω K S R W H c
  obtain ⟨⟨z, hz⟩, -⟩ := hΩ.omega1 K c.stand.mem
  have hmiss : ∀ J ∈ Ω, J ⊓ Q = ⊥ := by
    intro J hJ
    have hzQ : z ∉ Q := hN G Ω K S R W H c z hz Q hQn hQ2
    obtain ⟨g, hg⟩ := htrans J hJ
    by_contra hne
    have hzJ : IsUniqueInvolution J (g * z * g⁻¹) := by
      rw [← hg]
      exact hz.conj g
    have hA2 : IsPGroup 2 ↥(J ⊓ Q) := hQ2.to_inf_right
    have hcard : 2 ≤ Nat.card ↥(J ⊓ Q) := by
      have := (Subgroup.one_lt_card_iff_ne_bot (J ⊓ Q)).mpr hne
      omega
    have hmem : g * z * g⁻¹ ∈ J ⊓ Q :=
      AscL62.mem_of_uniqueInvolution_of_pGroup hzJ inf_le_left hA2 hcard
    apply hzQ
    have := hQn.conj_mem _ hmem.2 g⁻¹
    simpa [mul_assoc] using this
  refine ⟨?_, hmiss⟩
  have hJc : ∀ J ∈ Ω, J ≤ Subgroup.centralizer (Q : Set G) := fun J hJ =>
    normal_two_central_Q8 hΩ c.stand.cls c.stand.two hQ2 hJ (hmiss J hJ)
  have hle : (⨆ J ∈ Ω, J) ≤ Subgroup.centralizer (Q : Set G) := iSup₂_le hJc
  intro q hq'
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ ⨆ J ∈ Ω, J := by rw [hgen]; exact Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.mp (hle hg) q hq').symm
end Cent

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
