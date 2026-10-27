module

public import CFSG.ClassicalInvolution.Q3.Q3TWBHt
public import CFSG.ClassicalInvolution.Q3.Q3T8L274A

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Uniform

section Fuzzy

theorem fuzzyEdges3_of_hm {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : Q3T7M.HM Ω) : FuzzyEdges3 Ω := by
  intro M hM N hN a ha
  have hΩg : Disconnected.AschTight.HypOmegaGen Ω :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  have hMN : M ∈ omegaNbr Ω N := Q3CL.T3.omegaNbr_symm Q3T8.Asc77.l6_2 hΩ hM hN.1 hN
  obtain ⟨hNΩ, -, T, hT, hTN, hTM⟩ := hN
  obtain ⟨-, -, R', hR', hR'M, hR'N⟩ := hMN
  have hTsyl : IsSylow2In T N := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hNΩ hT hTN
  have hR'syl : IsSylow2In R' M := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hM hR' hR'M
  have h8 : 8 ≤ Nat.card R' := hΩ.eight_le_of_mem_RSet hR'
  have haR' : a ∈ R' := T3.mem_of_isPGroup ha hR'M hR'syl.2.1 (by omega)
  have haN : a ∈ Subgroup.normalizer (N : Set G) := hR'N haR'
  have hX : T8.XMem Ω a N := ⟨hNΩ, haN, T, hTsyl, fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (T3.le_centralizer_of_le_normalizer' ha hTM hr)⟩
  exact Balance.Bootstrap.mem_trivialOnQuot_iff_actsTrivOnQuot.mp
    (T8.XMem.trivialOnQuot3 hΩg ha.sq hX)

end Fuzzy

section Convert

theorem TwinFrameHyp51tC.toNA (h : TwinFrameHyp51tC) : TwinFrameHyp51tNA :=
  fun G _ _ _ Ω K K' J z u t hs => h G Ω K K' J z u t hs (fuzzyEdges3_of_hm hs.hyp)

theorem TwinFrameHyp51uC.toNA (h : TwinFrameHyp51uC) : TwinFrameHyp51uNA :=
  fun G _ _ _ Ω K K' J z u t hs => h G Ω K K' J z u t hs (fuzzyEdges3_of_hm hs.hyp)

theorem TwinFrameHyp51tC.toGeneric (h : TwinFrameHyp51tC) : TwinFrameHyp51t :=
  h.toNA.toGeneric

theorem TwinFrameHyp51uC.toGeneric (h : TwinFrameHyp51uC) : TwinFrameHyp51u :=
  h.toNA.toGeneric

theorem twinFrameHyp51t_proved : TwinFrameHyp51t :=
  twinFrameHyp51tC_proved.toGeneric

end Convert

end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
