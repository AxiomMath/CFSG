module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.MainNoBM
public import CFSG.Yardstones.Mdac756b924db.Definitions
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTwoGroupAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThree
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactWiring3Griess

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

section Open



theorem gl83GenericU3PlaneE3_of_open_noBM
    (hWC : KFactWeakClosure) (h123 : KFactWeakClosureHeis)
    (hK1 : StronglyEmbeddedRankTwoKFactNoBM) (hK2 : StronglyEmbeddedCyclicOuterKFact)
    (h07 : CFSG.Yardstones.Mdac756b924db.GL83GenericListSporE3) :
    CFSG.Yardstones.Mdac756b924db.GL83GenericU3PlaneE3 := by
  have h2324 := CFSG.RankThree.PartOne.sectionsForceEvenRankFour_fi23_fi24prime
    CFSG.RankThree.PartOne.sectionsForceEvenRankFour_Fi22
    CFSG.RankThree.PartOne.hasSection_fi23_fi22 CFSG.RankThree.PartOne.hasSection_fi24prime_fi23
  have hsec : SporSectionFacts3 :=
    ⟨CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group,
      CFSG.RankThree.PartOne.sectionsForceEvenRankFour_Fi22, h2324.1, h2324.2,
      CFSG.RankThree.PartOne.sectionsForceEvenRankFour_B,
      CFSG.RankThree.PartOne.simplePresentationM_sections_of_B_section
        CFSG.RankThree.PartOne.sectionsForceEvenRankFour_B
        CFSG.RankThree.PartOne.simplePresentationMHasBSection_holds⟩
  intro G _ _ hS hD1 hU0
  exact gl83GenericU3Plane_of_noBM hS hD1 hU0
    KFactProofs.Stroth.InnerAction.kFactInnerAction_holds hWC h123
    KFactProofs.Stroth.TwoSignalizer.signalizerTwoGroupKFact_holds hK1 hK2 kFactOutCyclic_holds
    (kF1At_of_griess CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds hS)
    (noExcludedSection3_of_sections hsec hS.rank) (h07 G hS hD1 hU0)

end Open

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
