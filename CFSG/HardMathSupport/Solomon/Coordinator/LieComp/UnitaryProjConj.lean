module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzUE
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Cover
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.FamilyProved
public import CFSG.HardMathSupport.Seitz.G2Noninner.Descent.OddNeThree
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.Final
public import CFSG.LieType.SeitzGeneration.ExcOuterAssemblyV5
public import CFSG.LieType.SeitzGeneration.OmegaF2.Basic
public import CFSG.LieType.SeitzGeneration.OuterSpPair
public import CFSG.LieType.SeitzGeneration.RootPairOrthBlock
public import CFSG.LieType.SeitzGeneration.RootPairSp
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCyc
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorLie
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
public import CFSG.RankThree.PartOne.Census3.Assembly
public import CFSG.RankThree.PartOne.FOC.Cases
public import CFSG.RankThree.PartOne.FOC.CompEquiv
public import CFSG.RankThree.PartOne.FOC.PSLFamily
public import CFSG.RankThree.PartOne.FOC.PSLLie
public import CFSG.RankThree.PartOne.FOCD.G2OddQPlus
public import CFSG.RankThree.PartOne.FOCD.PRank
public import CFSG.RankThree.PartOne.KC.UnitaryDefining
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartOne.SEITZ11.G2OddFinal
public import CFSG.RankThree.PartOne.SEITZ7.D4Wire
public import CFSG.RankThree.PartOne.SEITZ7.SlPair
public import CFSG.RankThree.PartOne.SEITZ7.SzPairK
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofExc
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec19
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec4
public import CFSG.RankThree.PartTwo.Sec19.Step1914Split
public import CFSG.RankThree.PartTwo.Sec4.E27.Core
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzOther
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzRest
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofSeitzSz
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate16041
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2136
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2145
public import Certificates.Certificate2323
public import Certificates.Certificate8160
public import Certificates.Certificate9124

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open Matrix CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz

variable {a n : ℕ} {E : Type} [Field E]

theorem congr_statedProjEquivPrimeFormOne_projConj (h : UnitaryFieldData 2 n E) (ha : 1 ≤ a)
    (M : GL (Fin a) E)
    (hN : M ∈ Subgroup.normalizer (unitarySU 2 n E a : Set (GL (Fin a) E)))
    (c : Eˣ)
    (hNunitary : (GeneralLinearGroup.scalar (Fin a) c * M : GL (Fin a) E) ∈
      primeFormUnitary h ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)) :
    MulAut.congr
        (show LargeEvenProj (unitarySU 2 n E a) ≃* primeFormP h
            ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) from
          statedProjEquivPrimeFormOne h ha)
        (TableB.projConj (unitarySU 2 n E a) ⟨M, hN⟩) =
      primeFormConjHom h ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)
        ⟨GeneralLinearGroup.scalar (Fin a) c * M, hNunitary⟩ := by
  set e : LargeEvenProj (unitarySU 2 n E a) ≃* primeFormP h
      ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) :=
    statedProjEquivPrimeFormOne h ha with he
  refine MulEquiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := e.surjective x
  induction y using QuotientGroup.induction_on with
  | H g =>
    rw [he]
    change statedProjEquivPrimeFormOne h ha
        (TableB.projConj (unitarySU 2 n E a) ⟨M, hN⟩ (QuotientGroup.mk g)) =
      primeFormConjHom h ((1 : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)
        ⟨GeneralLinearGroup.scalar (Fin a) c * M, hNunitary⟩
        (statedProjEquivPrimeFormOne h ha (QuotientGroup.mk g))
    rw [TableB.projConj_mk, statedProjEquivPrimeFormOne_mk, statedProjEquivPrimeFormOne_mk,
      primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    show (M : GL (Fin a) E) * (g : GL (Fin a) E) * M⁻¹ =
      (GeneralLinearGroup.scalar (Fin a) c * M) * (g : GL (Fin a) E) *
        (GeneralLinearGroup.scalar (Fin a) c * M)⁻¹
    have hX : Commute ((M : GL (Fin a) E) * (g : GL (Fin a) E) * M⁻¹)
        (GeneralLinearGroup.scalar (Fin a) c) :=
      commute_scalar c ((M : GL (Fin a) E) * (g : GL (Fin a) E) * M⁻¹)
    calc (M : GL (Fin a) E) * (g : GL (Fin a) E) * M⁻¹
        = (GeneralLinearGroup.scalar (Fin a) c *
              ((M : GL (Fin a) E) * (g : GL (Fin a) E) * M⁻¹)) *
            (GeneralLinearGroup.scalar (Fin a) c)⁻¹ := by
          rw [← hX.eq, mul_inv_cancel_right]
      _ = (GeneralLinearGroup.scalar (Fin a) c * M) * (g : GL (Fin a) E) *
            (GeneralLinearGroup.scalar (Fin a) c * M)⁻¹ := by group

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

end
