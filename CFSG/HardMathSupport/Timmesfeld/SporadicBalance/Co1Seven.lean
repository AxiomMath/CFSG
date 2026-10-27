module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1SevenBase
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts
public import Certificates.Certificate2043
public import Certificates.Certificate3024
public import Certificates.Certificate13696
public import Certificates.Certificate13697
public import Certificates.Certificate13698
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate8026Base
public import Certificates.Certificate9124

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint


theorem oPrimeCoreTrivialAt_seven_Co1 :
    OPrimeCoreTrivialAt 7 NativeSporadic.Co1 :=
  have h : OPrimeCoreTrivialAt 7 ↥CFSG.Sporadic.Co1Schreier.GA :=
    Co1S.oPrimeCoreTrivialAt_GA Certificates.certificate13696
      Certificates.certificate13697.2.2.2.1 Certificates.certificate13698.2.2.1
  @OPrimeCoreTrivialAt.of_mulEquiv 7 NativeSporadic.Co1 _ ↥CFSG.Sporadic.Co1Schreier.GA
    (Subgroup.toGroup CFSG.Sporadic.Co1Schreier.GA) CFSG.Sporadic.Co1Block.co1MatEquiv h

theorem sporadicOPrimeHolds_Co1_seven :
    SporadicOPrimeHolds .Co1 7 :=
  fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv e oPrimeCoreTrivialAt_seven_Co1

theorem isPGroup_centralizer_of_card_eq_49_Co1 :
    ∀ P : Subgroup NativeSporadic.Co1, Nat.card P = 49 →
      IsPGroup 7 ↥(Subgroup.centralizer (P : Set NativeSporadic.Co1)) :=
  @isPGroup_centralizer_of_mulEquiv 7 NativeSporadic.Co1 ↥CFSG.Sporadic.Co1Schreier.GA
    Units.instGroup (Subgroup.toGroup CFSG.Sporadic.Co1Schreier.GA)
    CFSG.Sporadic.Co1Block.co1MatEquiv 49
    (fun P hP => Co1S.isPGroup_centralizer_GA Certificates.certificate13696
      Certificates.certificate13697.2.2.2.2.1 P hP)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
