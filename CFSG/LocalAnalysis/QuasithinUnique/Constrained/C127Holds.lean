module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltEvenHolds
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltSlice
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113K.DetCatalog
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FFGlaubermanNiles
public import CFSG.Quasithin.Background.E2TwoProofSporTen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Main
public import CFSG.Quasithin.EmptyFaithful.A38c15IrrClose
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Final
public import CFSG.Quasithin.EmptyFaithful.E22NJ4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113K.Det
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Reduction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.C127Block.Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.OddCovers

public section

namespace CFSG.Quasithin

theorem theoremC127_holds :
    TheoremC127 :=
  theoremC127_of_ff B113KDet.catalogBridge_holds
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.ffModuleTheorem_holds
      QuasithinUnique.Bridge.asB42DichotomyNat_proved LieOver.asLieTwo_holds.1
      LieOver.asLieTwo_holds.2
      (c127KBlockType_of B15P4.asB15Part4
          (B69K.asB69ComponentK_of B113KDet.catalogBridge_holds
              CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.ffModuleTheorem_holds asB42_holds
              asA21SQTKSection E2P.e22AltFam E2P.e22LnTwoFam E2P.e22Char2ExcFam
              (E2P.e22Families_of_cited
                  (E2P.Asc80.asc80L3Eps_holds A38c15.sl3OddIrr A312U3.su3OddIrr_holds)
                  E2P.asc86bSporadic_holds) B69K.asSQTKOddCovers_holds B69K.asAltEven_holds
              (B69K.asAltSlice_of
                  (HardMathSupport.Cooperstein.Coordinator.EightFive.gf2EightFive_of_b42L42Core
                      HardMathSupport.Cooperstein.Coordinator.EightFive.b42L42Core_holds))))

end CFSG.Quasithin
