module

public import CFSG.CGT.PushingUpLit.CGT6.EmbSpineFinal
public import CFSG.CGT.PushingUpLit.CGT6.EmbLayerIrr
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndFooteU4
public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspExc
public import CFSG.RankThree.PartOne.Mult.Exceptional
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSporThree
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenWeilFinal
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M4
public import CFSG.CGT.PushingUpLit.CGT6.Diag.Assembly
public import CFSG.CGT.PushingUpLit.CGT6.Diag.NatMain
public import CFSG.CGT.PushingUpLit.CGT6.Diag.CountMain
public import CFSG.CGT.PushingUpLit.CGT6.Diag.IdentMain
public import CFSG.CGT.PushingUpLit.CGT6.Diag.S2Main
public import CFSG.CGT.PushingUpLit.CGT6.Diag.BoundSL
public import CFSG.CGT.PushingUpLit.CGT6.Diag.BoundAlt
public import CFSG.CGT.PushingUpLit.CGT6.Diag.BoundMinus
public import CFSG.CGT.PushingUpLit.CGT6.Diag.ConsCore
public import CFSG.CGT.PushingUpLit.CGT6.Diag.ConsMinus
public import CFSG.CGT.PushingUpLit.CGT6.Diag.ConsAlt
public import CFSG.CGT.PushingUpLit.CGT6X.End4A7
public import CFSG.CGT.PushingUpLit.CGT6X.End4A9
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltFinal
public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusMain
public import CFSG.CGT.PushingUpLit.CGT6.RouteCEnd
public import CFSG.CGT.PushingUpLit.CGT6.RouteCFin
public import CFSG.CGT.PushingUpLit.CGT6.Emb5Ten
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.CGT.PushingUpLit.CGT6K1.Dispatch
public import CFSG.CGT.PushingUpLit.CGT6K1.PrimedL3U3
public import CFSG.CGT.PushingUpLit.CGT6K1.PrimedG23
public import CFSG.CGT.PushingUpLit.CGT6K1.PrimedL2

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG CFSG.RankThree.PartOne CFSG.ComponentClassification CFSG.CGT.PushingUpLit.CGT6
  CFSG.CGT.PushingUpLit.CGT6X
open CFSG.CGT.PushingUpLit.CGT6X.End3 CFSG.CGT.PushingUpLit.CGT6X.End4
open CFSG.ComponentClassification.AschbacherKnownGroup (AschbacherKnownGroupFacts)

theorem aschbacherEmbeddingK_of_simpleOutcome
    (h5 : GSThmB.AschbacherTheorem5Input) (hK : AschbacherKnownGroupFacts)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Assembly.InCatalog)
    (hT4 : AS76b.Asc75Theorem4)
    (hOut : SimpleOutcome) (hGA : CFSG.Open.GriessAllModelsStatement) (hFoote : EndFoote)
    (hK3 : CFSG.ComponentClassification.RankTwoStandard.RankTwoAlternatingStandard)
    (hA : AltCaseA)
    (K5 : StellmacherSixOneThree) : AschbacherEmbeddingK := by
  have h47 : FourSeven := fun V _ _ hV G T Y cfg X hXG hX hYX =>
    emb_four_seven_of_m4 schurMultL2Two_holds hV cfg hXG hX hYX
  have h2 : Stage2Out :=
    stage2Out_of_steps (step49_of_inputs h5 hK hS schurMultL2Two_holds)
      (step410_of_diag hS h47 (diagFree_of_parts (diagReduction_of_schreier hS schurMultL2Two_holds)
          diagModIrr_holds (diagModAlt_of diagModSel_holds diagBoundAlt_holds)
          (diagModMinus_of diagModSel_holds diagModS2_holds diagBoundMinus_holds)
          (diagModCore_of diagModSel_holds diagModS2_holds diagBoundSL_holds diagModIdent_holds)
          diagModNat_holds diagModCount_holds)) (end4OmegaPlus_of_inputs h5 hK hS hT4)
  have h3 : EndFour :=
    endFour_of_cases' (endGMS'_of_inputs schurMultL2Two_holds TCB.tauCetiCatalogBridge hOut)
      end411_holds' end412_holds' end413_holds'
      (end415_of_exc h1NaturalSL2_holds schurMultL2Two_holds hGA hFoote
        (footeInspExc_of (Mult.exceptionalCenterSmallPrimes_of_griess hGA)))
      (end4Small_m12 sporadicThreeCenterSmallPrimes_holds)
      (end4Small_j1 sporadicThreeCenterSmallPrimes_holds)
      (end4Small_j2 sporadicThreeCenterSmallPrimes_holds) end4Small_a9 end4Small_a7
      (end4Small_l225 sporadicThreeCenterSmallPrimes_holds)
      (end4Small_l35 sporadicThreeCenterSmallPrimes_holds)
      (end4Small_u35 sporadicThreeCenterSmallPrimes_holds)
      (end4Alt_of_caseA_inputs TCB.tauCetiCatalogBridge hK3 natLift_holds hA)
  exact aschbacherEmbeddingK_of_stages h2 h3
    (emb5End_of_routeC natLift_holds natRecog_holds (fun n h2 h6 => finC n h2 h6)
      (emb5Ten_of_k5 K5))

end CFSG.CGT.PushingUpLit.CGT6K1
