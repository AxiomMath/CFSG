module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.Leaves
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairPSL
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairPSU
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairPSp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairF4
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairE6
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Pair2E6
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairE8
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairE7Final

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG.Open CFSG.ComponentClassification

theorem hasClassBMember_of_quotient {L : Type} [Group L] [Finite L]
    (h : HasCleanFullClassBMember (L ⧸ center L)) : HasClassBMember L :=
  (h.lift (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _).le).hasClassBMember

section


theorem hasClassBMember_of_hrF3 (hGA : TBLit.GriessMultipliersAllModels)
    (hC2 : POmegaPlusCentreExpTwo) (hC4 : POmegaPlusNotLinUnit) {L : Type} [Group L] [Finite L]
    [IsSimpleGroup (L ⧸ center L)] (h : HRF3HigherRank (L ⧸ center L)) : HasClassBMember L := by
  obtain ⟨τ, n, hm, hcases⟩ := h
  rcases hcases with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ |
    rfl | rfl | rfl | rfl | rfl
  · exact hasClassBMember_of_quotient (hasCleanFullClassBMember_of_lieModel_psl hGA hn hm)
  · exact hasClassBMember_of_quotient (hasCleanFullClassBMember_of_lieModel_psu hGA hn hm)
  · exact hasClassBMember_of_quotient (hasCleanFullClassBMember_of_lieModel_psp hGA hn hm)
  · exact (hasPOmegaClassBMember_of_lieModel_pomega_quotient hC2 hC4 (Or.inl ⟨rfl, hn⟩)
      hm).hasClassBMember
  · exact (hasPOmegaClassBMember_of_lieModel_pomega_quotient hC2 hC4
      (Or.inr (Or.inl ⟨rfl, hn⟩)) hm).hasClassBMember
  · exact (hasPOmegaClassBMember_of_lieModel_pomega_quotient hC2 hC4
      (Or.inr (Or.inr ⟨rfl, hn⟩)) hm).hasClassBMember
  · obtain rfl : n = 0 := hm.admissible.2.2
    exact hasClassBMember_of_quotient (hasCleanFullClassBMember_of_lieModel_f4 hGA hm)
  · obtain rfl : n = 0 := hm.admissible.2.2
    exact hasClassBMember_of_quotient (hasCleanFullClassBMember_of_lieModel_e6 hGA hm)
  · obtain rfl : n = 0 := hm.admissible.2.2
    exact (hasPOmegaClassBMember_of_lieModel_e7_quotient hC2 hC4 hm).hasClassBMember
  · obtain rfl : n = 0 := hm.admissible.2.2
    exact hasClassBMember_of_quotient (hasCleanFullClassBMember_of_lieModel_e8 hGA hm)
  · obtain rfl : n = 0 := hm.admissible.2.2
    exact hasClassBMember_of_quotient (hasCleanFullClassBMember_of_lieModel_twistedE6 hGA hm)

end

end CFSG.OddStandard.HigherRank.F3
