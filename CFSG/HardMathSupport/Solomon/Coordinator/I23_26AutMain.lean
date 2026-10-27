module

public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26AutFrame
public import CFSG.HardMathSupport.Solomon.Proving.ExtremalCentre
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26AutBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.AutL3
  CFSG.Quasithin.A318P CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_stdModel_of_quot {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (hExt : IsExtremalType (K ⧸ Subgroup.center K)) : StdModelL K ∨ StdModelU K := by
  have hZ : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    Proving.center_eq_bot_of_isExtremalType hExt
  have hQ := isQuasisimple_quotient_center hK
  rcases exists_stdModel hQ (Or.inl hExt) with ⟨F, _, _, h3, ⟨e⟩⟩ |
      ⟨p, f, F, _, hF, hq, h3, ⟨e⟩⟩
  · exact Or.inl ⟨F, inferInstance, inferInstance, h3, ⟨(barEquivBot hZ).symm.trans e⟩⟩
  · exact Or.inr ⟨p, f, F, inferInstance, hF, hq, h3, ⟨(barEquivBot hZ).symm.trans e⟩⟩

theorem autL3ElemStructure_holds : AutL3ElemStructure := by
  intro K _ _ hK hExt E hE hcard
  rcases exists_stdModel_of_quot hK hExt with ⟨F, _, _, h3, ⟨ε⟩⟩ |
      ⟨p, f, F, _, hF, hq, h3, ⟨ε⟩⟩
  · have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
    exact autStruct_of_frame hK ε (l3FrameLinear h3) (fun E hED hE => hD9_L h3 E hED hE)
      (fun α h c _ hform => Or.inr (Or.inl (isFieldAutPSL3_of_model ε c h hform)))
      (fun α hα => Or.inl (isInnDiagPSL3_of_model ε hα)) E hE hcard
  · have hfin := hF.finite
    have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
    exact autStruct_of_frame hK ε (l3FramePSU hF hq h3) (fun E hED hE => hD9_U hF h3 E hED hE)
      (fun α h c hc hform => Or.inr (Or.inr (isFieldAutPSU3_of_model hF ε c
        (by rw [hc]; decide) h hform)))
      (fun α hα => Or.inr (isInnDiagPSU3_of_model hF ε hα)) E hE hcard

end CFSG.HardMathSupport.Solomon.Coordinator
