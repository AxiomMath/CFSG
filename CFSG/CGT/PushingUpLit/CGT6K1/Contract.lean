module

public import CFSG.CGT.PushingUpLit.CGT6K1.ContractCore
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbFinal
public import CFSG.CGT.PushingUpLit.CGT6K1.Alpha1
public import CFSG.CGT.PushingUpLit.CGT6K1.Closed
public import CFSG.CGT.PushingUpLit.CGT6K1.Transfer
public import CFSG.CGT.PushingUpLit.CGT6K1.InnerClosed
public import CFSG.CGT.PushingUpLit.CGT6K1.Rank2
public import CFSG.LocalAnalysis.ComponentClassification.GMS78GapHKSAffineProof
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4Boundary
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4HomoResT0
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4RootCore
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG CFSG.RankThree.PartOne CFSG.ComponentClassification CFSG.CGT.PushingUpLit.CGT6
  CFSG.CGT.PushingUpLit.CGT6X
open CFSG.ComponentClassification.AschbacherKnownGroup (AschbacherKnownGroupFacts)


theorem aschbacherEmbeddingK_of_inputs'
    (h5 : GSThmB.AschbacherTheorem5Input) (hK : AschbacherKnownGroupFacts)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Assembly.InCatalog)
    (hT4 : AS76b.Asc75Theorem4)
    (hK1'' : StdKernelTwo) (hGA : CFSG.Open.GriessAllModelsStatement) (hFoote : EndFoote)
    (hK3 : CFSG.ComponentClassification.RankTwoStandard.RankTwoAlternatingStandard)
    (K5 : StellmacherSixOneThree) : AschbacherEmbeddingK := by
  have hSel : CatSelector := catSelector_holds
  have hSimple : SimpleStd :=
    simpleStd_of_inputs hSel innerSurvivorsInV_holds (rank2Std_of_inputs
        (GMS78.l2Res_of_gms42ResidualU
            ⟨RankTwoFoundation.lemma32, RankTwoFoundation.lemma33One, RankTwoFoundation.lemma33Two,
                RankTwoFoundation.lemma33Three, RankTwoFoundation.asc75Theorem4⟩
            GMS78.hksRegularNormalAffine
            (GMS78.gms42ResidualU_of GMS78.gms42ResidualT0 GMS78.gms42ResidualRoot)) hK3) hK1''
  exact aschbacherEmbeddingK_of_simpleOutcome h5 hK hS hT4
    (fun Q _ _ n A T₀ h => simpleOuterOutcome_of_inputs hSel hSimple h) hGA hFoote hK3
    (altCaseA_holds TCB.tauCetiCatalogBridge hK3 natLift_holds) K5

end CFSG.CGT.PushingUpLit.CGT6K1
