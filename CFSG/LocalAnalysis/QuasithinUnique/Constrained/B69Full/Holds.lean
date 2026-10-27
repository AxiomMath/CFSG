module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69Full.Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltEvenHolds
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltSlice
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113K.DetCatalog
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FFGlaubermanNiles
public import CFSG.Quasithin.Background.E2TwoProofSporTen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Main
public import CFSG.Quasithin.EmptyFaithful.A38c15IrrClose
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Final
public import CFSG.Quasithin.EmptyFaithful.E22NJ4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.OddCovers

public section

namespace CFSG.Quasithin

theorem b_6_9_holds
    : CFSG.ASVolI.B_6_9 :=
  b_6_9_of_compK (B69K.asB69ComponentK_of B113KDet.catalogBridge_holds
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.ffModuleTheorem_holds asB42_holds
      asA21SQTKSection E2P.e22AltFam E2P.e22LnTwoFam E2P.e22Char2ExcFam
      (E2P.e22Families_of_cited (E2P.Asc80.asc80L3Eps_holds A38c15.sl3OddIrr A312U3.su3OddIrr_holds)
          E2P.asc86bSporadic_holds) B69K.asSQTKOddCovers_holds B69K.asAltEven_holds
      (B69K.asAltSlice_of
          (HardMathSupport.Cooperstein.Coordinator.EightFive.gf2EightFive_of_b42L42Core
              HardMathSupport.Cooperstein.Coordinator.EightFive.b42L42Core_holds)))

end CFSG.Quasithin
