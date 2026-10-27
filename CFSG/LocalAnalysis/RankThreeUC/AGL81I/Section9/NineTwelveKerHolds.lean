module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveKer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTwelveOneSettingGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTwelveTwoGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixSevenHolds
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.GLThreeHolds
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.SpFourHolds
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.Solvable
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Holds
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Sp4.Main
public import CFSG.RankThree.PartOne.KF.BloomClose
public import CFSG.RankThree.PartOne.A6N.Final
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenInputsHolds
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.GroupTheory.CoprimeLiftElementaryAbelian
public import CFSG.GroupTheory.GL52.SylowTools
public import CFSG.GroupTheory.RegularModuleThree
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Rest
public import CFSG.LieType.OutStructureLinearDiagonal
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Weak
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SevenFourTwoOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACz
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Alt
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSU
public import CFSG.RankThree.PartTwo.KFacts.K71OddChar

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C


theorem nineTwelveKerGen_of_inputs (hI : NineTenInputs) (h67 : SixSeven)
    (hres : NineTwelveThirteenRankThree) (hsec : NineSixAutSectionGen)
    (hK3 : KFactAutRankThreeSolvable)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog) :
    NineTwelveKerGen :=
  fun _ _ _ _ _ _ _ _ h hH2 hp =>
    ⟨fun hL _ hLK => h.nineTwelveOne hsec hK3 hS hH2 hp hL hLK,
      fun hL _ hR => h.nineTwelveTwoKer hI h67 hres hH2 hp hL hR⟩

theorem nineTwelveKerGen_holds
    (hres : NineTwelveThirteenRankThree) :
    NineTwelveKerGen :=
  nineTwelveKerGen_of_inputs nineTenInputs_holds sixSeven_holds hres
    (nineSixAutSectionGen_of lowDimMulAutSection_holds
      (nineSixLowDimSectionGen_of (NineSixKFact.kFactLowDimPPrimeGen_of
          CFSG.RankThree.PartOne.extBloomMitchell_holds
          CFSG.RankThree.PartOne.A6N.kf1322ThreeA6Norm_holds NineSixKFact.pSpFourPPrimeGen)))
    (kFactAutRankThreeSolvable_of glIrrQuasisimpleThreeDvd_holds spFourQuasisimpleThreeDvd_holds) CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
