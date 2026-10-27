module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Main
public import CFSG.Yardstones.Mdac756b924db.Definitions
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupMcLLem45Certificate
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Gamma
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma42ClassNoBM
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTwoGroupAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThree
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactWiring3Griess

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

section Open

theorem gl83GenericListSporE3_of_class
    (h123 : Generic49U3.KFactWeakClosureHeis)
    (hClass : ∀ (G : Type) [Group G] [Finite G], Setting G → FullCoreLocal G →
      Generic49U3.GenericComponentClass G)
    (hI : KFactI1434) (hU : KFactU44Data)
    (hI6103 : KFactI6103Five) (hI122 : KFactI122Five) (hI713 : KFactI713Out)
    (hNonab : KFactNonabF5) :
    CFSG.Yardstones.Mdac756b924db.GL83GenericListSporE3 := by
  intro G _ _ hS hD1 hU0
  have hK : TypeIIKFacts :=
    ⟨KFactProofs.Stroth.InnerAction.kFactInnerAction_holds,
      KFactProofs.Stroth.WeakClosure.kFactWeakClosure_holds, h123,
      KFactProofs.Stroth.TwoSignalizer.signalizerTwoGroupKFact_holds⟩
  exact genericListSpor_of_types hS hD1 hU0 hK (hClass G hS hU0) tits_gfree a10_gfree
    mcl_gfree_certified j4_gfree sz32_gfree.1 sz32_gfree.2 sz32DataFacts_holds
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds hI hU a10Ext_holds hI6103 hI122 hI713
    hNonab

theorem gl83GenericListSporE3_of_open_noBM
    (h123 : Generic49U3.KFactWeakClosureHeis)
    (hK1 : StronglyEmbeddedRankTwoKFactNoBM) (hK2 : StronglyEmbeddedCyclicOuterKFact)
    (hI : KFactI1434) (hU : KFactU44Data)
    (hI6103 : KFactI6103Five) (hI122 : KFactI122Five) (hI713 : KFactI713Out)
    (hNonab : KFactNonabF5) :
    CFSG.Yardstones.Mdac756b924db.GL83GenericListSporE3 := by
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
  exact gl83GenericListSporE3_of_class h123
    (fun G _ _ hS hU0 =>
      Generic49U3.genericComponentClass_of_inputs_noBM hS hU0 hK1 hK2 kFactOutCyclic_holds
        (kF1At_of_griess CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds hS)
        (noExcludedSection3_of_sections hsec hS.rank))
    hI hU hI6103 hI122 hI713 hNonab

end Open

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
