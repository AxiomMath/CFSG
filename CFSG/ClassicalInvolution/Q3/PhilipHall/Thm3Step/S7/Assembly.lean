module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.LieSame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoFinal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.AEmpty

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

section Assembly


theorem thm3RTwoClass_of_ident' (hT : S7Ident.TwoOrbitOfIdent') (hI : InspectionFacts)
    (hR : RowClassAEmpty) (m : ℕ) : Thm3RTwoClass m := by
  intro Y _ _ Φ K hc _ h2 hF hcl hG
  have hid : ∀ M ∈ Φ, ∀ z : Y, IsUniqueInvolution M z →
      ∃ hzH : z ∈ omegaGen (S7Ident.lOrbit (genFittingFStar Y) M),
        S7Ident.OrbitIdent ↥(omegaGen (S7Ident.lOrbit (genFittingFStar Y) M))
          (M.subgroupOf (omegaGen (S7Ident.lOrbit (genFittingFStar Y) M))) ⟨z, hzH⟩ := by
    intro M hM z hz
    obtain ⟨hzH, h⟩ :=
      S7Ident.orbitHyp_of_ctx hc h2 hF hM (aEmpty_lOrbit hR hc h2 hF hcl hM) hz
    refine ⟨hzH, S7Ident.orbitIdent_of_stepIH hc.ih ?_ h⟩
    rw [← hc.card]
    exact Subgroup.card_le_card_group _
  obtain ⟨J, hJ, hJK⟩ : ∃ J ∈ Φ, J ∉ S7Ident.lOrbit (genFittingFStar Y) K := by
    by_contra hno
    exact hcl fun N hN => by_contra fun h => hno ⟨N, hN, h⟩
  have hcit : CIT3Below (Nat.card Y + 1) := hc.card ▸ hc.ih.cit
  obtain ⟨hmod, rfl⟩ := hT Y hcit hc.odd h2 hF Φ hc.hyp hc.gen hid K hc.mem J hJ hJK hG
  exact hI Y hmod K hc.mem

theorem thm3RTwoClass_of_facts (hOC : S7Ident.SocleOddCore) (hTO : S7Ident.TwinOddCore)
    (hL33 : S7Ident.L33Q8Class) (hU3 : S7Ident.U33Q8Classes) (hM12 : S7Ident.M12Q8Classes)
    (hTQ : S7Ident.TwinQ8Class) (hI : InspectionFacts) (hR : RowClassAEmpty) (m : ℕ) :
    Thm3RTwoClass m :=
  thm3RTwoClass_of_ident' (S7Ident.twoOrbitOfIdent'_of_finite S7Ident.twoLieOrbitsSame_proved hOC
    hTO hL33 hU3 hM12 hTQ) hI hR m

end Assembly

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7
