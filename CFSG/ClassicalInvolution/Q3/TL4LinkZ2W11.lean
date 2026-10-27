module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W10
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2S
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4OG
public import CFSG.ClassicalInvolution.Q3.TL4StepDefs
public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWired27
public import CFSG.ClassicalInvolution.Q3.TL4LinkDiscC2
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W7

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

section Cit3


variable {n : ℕ}

theorem tightLinkZ2L2CoreR_of (hg : Z2GapFacts) (hP : TightBelowRPlus 3 n) (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) : TightLinkZ2L2CoreR n := by
  intro Y _ _ R S t hL hc hT hZ2 hsimp hidx hmod J hJ u hu hall
  obtain ⟨R₀, T₀, hR₀, hR₀u, hT₀, hT₀N, P, hR₀P, hT₀P⟩ := exists_adapted_sylow hL hJ hu
  have hs : Z2Set n R S t J u R₀ T₀ P := ⟨hL, hc, hT, hZ2, hsimp, hidx, hmod, hJ, hu, hR₀, hR₀u,
    hT₀, hT₀N, hall R₀ T₀ hR₀ hR₀u hT₀ hT₀N, hR₀P, hT₀P⟩
  have h1 := hs.c264One (tightLinkC264One_of_gaps hg) hP h4 htw
  by_cases hinv : ∃ b ∈ (P : Subgroup Y), b ∉ edgeCent (P : Subgroup Y) t u ∧ b * b = 1
  · exact hs.false_of_involution h1 hinv
  · exact hs.false_of_noInvolution h1 hall hinv

theorem tightLinkZ2L2OuterAllR_of_core (h : TightLinkZ2L2CoreR n) :
    TightLinkZ2L2OuterAllR 3 n :=
  fun Y _ _ R S t hL hc hT hZ2 hsimp hidx hmod J hJ u hu _ hall _ =>
    h Y R S t hL hc hT hZ2 hsimp hidx hmod J hJ u hu hall

theorem tightLinkZ2L2InnerR_of (hg : Z2GapFacts) (hP : TightBelowRPlus 3 n) (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) : TightLinkZ2L2InnerR 3 n := by
  intro Y _ _ R S t hL hc hT hZ2 hsimp hidx hmod J hJ u hu _ hall hinner
  obtain ⟨R₀, T₀, hR₀, hR₀u, hT₀, hT₀N, P, hR₀P, hT₀P⟩ := exists_adapted_sylow hL hJ hu
  have hs : Z2Set n R S t J u R₀ T₀ P := ⟨hL, hc, hT, hZ2, hsimp, hidx, hmod, hJ, hu, hR₀, hR₀u,
    hT₀, hT₀N, hall R₀ T₀ hR₀ hR₀u hT₀ hT₀N, hR₀P, hT₀P⟩
  have h1 := hs.c264One (tightLinkC264One_of_gaps hg) hP h4 htw
  obtain ⟨b, hbP, hbt⟩ := hs.exists_swap
  have hbA : b ∉ edgeCent (P : Subgroup Y) t u := by
    intro h
    have hbt' : b * t * b⁻¹ = t := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp h.1.2, mul_inv_cancel_right]
    exact hs.t_ne_u (hbt'.symm.trans hbt)
  have hbb := hs.mul_self_mem_edgeCent hbP
  have hin : InnerModOdd (linkLayer R t) (b * b) :=
    (hinner (b * b) (P.isPGroup'.to_le
      (Subgroup.zpowers_le.mpr ((P : Subgroup Y).mul_mem hbP hbP)))
      (Subgroup.mem_centralizer_singleton_iff.mp hbb.1.2)
      (Subgroup.mem_centralizer_singleton_iff.mp hbb.2)).1
  exact hs.false_of_involution h1 (hs.exists_involution_of_inner_sq hall hbP hbA hin)

theorem tightLinkZ2L2OuterR_of (hg : Z2GapFacts) (hP : TightBelowRPlus 3 n) (h4 : Thm4RBelow 3 n)
    (h5 : Thm5RBelowF 3 n) (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) :
    TightLinkZ2L2OuterR 3 n :=
  outer_of_outerAll h4 h5 htw e4AutOddFreeR_proved omegaAutOddFreeR_proved
    (tightLinkZ2L2OuterAllR_of_core (tightLinkZ2L2CoreR_of hg hP h4 htw))

end Cit3

theorem tightLinkZ2L2OuterR_plus_of_gaps
    (hg : Z2GapFacts) (n : ℕ) : TL4.PlusLeaf TL4.TightLinkZ2L2OuterR n := by
  intro hA hPlus
  exact tightLinkZ2L2OuterR_of hg hPlus
    (CFSG.ComponentClassification.QuaternionComponent.thm4RBelow₂₇ n hA hPlus) hPlus.thm5
    (hPlus.twin rfl)

theorem tightLinkZ2L2InnerR_plus_of_gaps
    (hg : Z2GapFacts) (n : ℕ) : TL4.PlusLeaf TL4.TightLinkZ2L2InnerR n := by
  intro hA hPlus
  exact tightLinkZ2L2InnerR_of hg hPlus
    (CFSG.ComponentClassification.QuaternionComponent.thm4RBelow₂₇ n hA hPlus) (hPlus.twin rfl)

end CFSG.ClassicalInvolution.Q3.TL4.Z2W
