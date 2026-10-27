module

public import CFSG.HardMathSupport.Solomon.Coordinator.I23_16FieldAut
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_16Defs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Lin
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Uni

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.AutL3
  CFSG.Quasithin.A318P CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.SBd19F

theorem field3Structure_holds : Field3Structure := by
  intro K _ _ hK hT
  rcases hT with ⟨F, _, _, ⟨e⟩⟩ | ⟨F, _, _, q, hcard, ⟨e⟩⟩
  · let ε : (K ⧸ Subgroup.center K) ≃* projectiveSL 3 F := e.trans (psiO F)
    refine ⟨fun α h3 => FieldThree.isInnDiagThree_or_isFieldAutThree_L ε h3, ?_⟩
    intro E hE hfield
    by_cases h3 : 3 ∣ Nat.card F - 1
    · have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
      exact FieldThree.card_le_three_of_frame hK ε (l3FrameLinear h3)
        (fun α hα => Or.inl (isInnDiagPSL3_of_model ε hα)) E hE hfield
    · refine FieldThree.card_le_three_of_outThreeBound hK ε
        (outThreeBound_psl3 F (by rw [Nat.card_units]; exact h3)) ?_ E hE hfield
      intro α hα hinner
      have h1 := (stdPinnedPSL 3 F).inn_le hinner
      rw [stdPinnedPSL_inndiag] at h1
      exact LocalBalance.AutL3.input7_fieldInnDiag_holds K hK α hα
        (Or.inl (isInnDiagPSL3_of_model ε h1))
  · obtain ⟨p, f, rfl, ⟨hF⟩⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.exists_unitaryFieldData hcard
    have hfin := hF.finite
    have hq : 2 < p ^ f := two_lt_pow_of_quasisimple hK hF (e.trans (psuO hF).symm)
    let ε : (K ⧸ Subgroup.center K) ≃* unitaryPSU hF 3 := e.trans (psuO hF).symm
    refine ⟨fun α h3 => FieldThree.isInnDiagThree_or_isFieldAutThree_U hF hq ε h3, ?_⟩
    intro E hE hfield
    by_cases h3 : 3 ∣ p ^ f + 1
    · have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
      exact FieldThree.card_le_three_of_frame hK ε (l3FramePSU hF hq h3)
        (fun α hα => Or.inr (isInnDiagPSU3_of_model hF ε hα)) E hE hfield
    · refine FieldThree.card_le_three_of_outThreeBound hK ε (outThreeBound_psu3 hF hq h3) ?_ E hE
        hfield
      intro α hα hinner
      have h1 := (stdPinnedPSU3 hF).inn_le hinner
      exact LocalBalance.AutL3.input7_fieldInnDiag_holds K hK α hα
        (Or.inr (isInnDiagPSU3_of_model hF ε h1))

end CFSG.HardMathSupport.Solomon.Coordinator
