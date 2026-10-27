module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Open
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI6103FiveHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.OpenNoBM
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI713OutMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI122FiveMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FiveDiagSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFBMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.K1NoBMHolds
public import CFSG.LieType.SeitzGeneration.SeitzOuterLowNProof
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5OmegaDefChar
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5OmegaClassical
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5OmegaExc
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5OmegaE8
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5OmegaE8Witness
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.U44DataHolds
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FieldGen5Main
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I714FourMain
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.NoM125Transfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuterAssembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

theorem gl83GenericListSporE3_of_i1434 (hI : KFactI1434) :
    CFSG.Yardstones.Mdac756b924db.GL83GenericListSporE3 :=
  gl83GenericListSporE3_of_open_noBM WeakClosureHeis.kFactWeakClosureHeis_holds
    CFSG.AGLEmbedding.stronglyEmbeddedRankTwoKFactNoBM_holds
    (KFactProofs.Stroth.CyclicOuter.stronglyEmbeddedCyclicOuter_of_seitzOuterLowN
      CFSG.LieType.SeitzGeneration.seitzOuterLowN_holds)
    hI kFactU44Data_holds kFactI6103Five_holds
    (kFactI122Five_of_inputs (Sylow5Omega.sylow5OmegaLie_of_cases Sylow5Omega.defCharCase_holds
        Sylow5Omega.classicalCase_holds Sylow5Omega.exceptionalCase_holds
        (Sylow5Omega.e8Case_of_witness Sylow5Omega.e8Witness_holds)) fiveDiagSylow) kFactI713Out_holds
    (kFactNonabF5_of_parts' kFactI6103Five_holds kFactNoM125Sylow'_holds kFactI714Four'_holds
      kFactFieldGeneration5_holds sz32Facts_holds sz32_sigOne)

theorem gl83GenericU3PlaneE3_of_i1434 (hI : KFactI1434) :
    CFSG.Yardstones.Mdac756b924db.GL83GenericU3PlaneE3 :=
  Generic49U3.gl83GenericU3PlaneE3_of_open_noBM
    KFactProofs.Stroth.WeakClosure.kFactWeakClosure_holds
    WeakClosureHeis.kFactWeakClosureHeis_holds
    CFSG.AGLEmbedding.stronglyEmbeddedRankTwoKFactNoBM_holds
    (KFactProofs.Stroth.CyclicOuter.stronglyEmbeddedCyclicOuter_of_seitzOuterLowN
      CFSG.LieType.SeitzGeneration.seitzOuterLowN_holds)
    (gl83GenericListSporE3_of_i1434 hI)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
