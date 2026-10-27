module

public import CFSG.GF2Type.Smith1979.W4InspNd
public import CFSG.GF2Type.Smith1979.W4InspOmega
public import CFSG.GF2Type.Smith1979.W4InspDeg
public import CFSG.LargeExtraspecial.S12InspPSLMain
public import CFSG.LargeExtraspecial.S12InspFamJ2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Insp

open Subgroup Module CFSG.LargeExtraspecial CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {S : Setting G} {g : G} {t : S.O}

theorem concl_of_nondeg
    (hc : Ctx S g t)
    (hnd : S.IsNondeg12 g)
    (hout : CFSG.Timmesfeld.Outcome (S.Xbar12 g)) : Concl S g t := by
  rcases Setting.irred_or_pslPair hc.ht hc.htA hc.hS hc.hred hnd with hirr | hP
  · rcases outcome_survivors hout (card_Xbar_dvd S g hc.hw) with
      h | h | h | h | h | h | h | h | h
    · exact (false_of_psl32 hc h).elim
    · exact (false_of_psl32_f2 hc h).elim
    · exact (Setting.psl_false_of_irred_four hc.hw h hirr).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (spSixSpin_of_psp3 hc h))))))
    · exact Or.inr (Or.inl ⟨hnd, case2_of_omega hc (Or.inl h)⟩)
    · exact Or.inr (Or.inl ⟨hnd, case2_of_omega hc (Or.inr h)⟩)
    · exact (false_of_psu33 hc hirr h).elim
    · obtain ⟨φ⟩ := h
      exact (Setting.false_of_mulEquiv_alt6 hc.ht hc.htA hc.hS φ).elim
    · exact (Setting.false_of_isSporadic_J2 hc.ht hc.htA hc.hS h).elim
  · obtain ⟨P⟩ := hP
    exact Or.inl (P.case1 hc.haQ hc.hne (by have := hc.hw; omega) hc.ht hc.htA hc.hS hc.hred)

omit [IsSimpleGroup G] in
theorem concl_of_deg (hc : Ctx S g t) (hdeg : ¬ S.IsNondeg12 g)
    (h : S12FischerConclusion (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g)) : Concl S g t := by
  rcases (s12FischerConclusion_iff _ _).mp h with h | h | h | h | h | h
  · exact concl_of_sym hc h
  · exact concl_of_sp hc hdeg h
  · exact concl_of_o hc h
  · exact concl_of_psu hc h
  · exact concl_of_f3 hc h
  · exact concl_of_fi hc h

theorem inspW4Input_holds :
    InspW4Input := by
  rw [inspW4Input_iff]
  intro G _ _ _ S g t hc hcls
  rcases hcls with ⟨hnd, hout⟩ | ⟨hdeg, hF⟩
  · exact concl_of_nondeg hc hnd hout
  · exact concl_of_deg hc hdeg hF

theorem timmesfeld12_3InspectionInput_of_insp5
    (h5 : Insp5Input) : Timmesfeld12_3InspectionInput :=
  timmesfeld12_3InspectionInput_of_split inspW4Input_holds h5

end CFSG.GF2Type.Smith1979.W4Insp
