module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1FiveBase
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts
public import Certificates.Certificate2043
public import Certificates.Certificate3024
public import Certificates.Certificate13670
public import Certificates.Certificate13671
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

local notation "Rows" => CFSG.Sporadic.Co1Schreier.Native.Rows

theorem oPrimeCoreTrivialAt_Co1_five :
    OPrimeCoreTrivialAt 5 NativeSporadic.Co1 :=
  have h : OPrimeCoreTrivialAt 5 ↥CFSG.Sporadic.Co1Schreier.GA :=
    Co1F.oPrimeCoreTrivialAt_GA Certificates.certificate13670
  @OPrimeCoreTrivialAt.of_mulEquiv 5 NativeSporadic.Co1 _ ↥CFSG.Sporadic.Co1Schreier.GA
    (Subgroup.toGroup CFSG.Sporadic.Co1Schreier.GA) CFSG.Sporadic.Co1Block.co1MatEquiv h

theorem sporadicOPrimeHolds_Co1_five :
    SporadicOPrimeHolds .Co1 5 :=
  fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv e oPrimeCoreTrivialAt_Co1_five

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
