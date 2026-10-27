module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.L2
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.SzTits
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.RankInn
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutSp
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutOrth
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutReeF4
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutD4
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnLinOutDiag
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnUniOutDiag
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnSp
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnOrth
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnF4
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnE6Plumb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnE6TwPlumb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnE6Kinds
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnE7
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnE8

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

theorem up34Chev2Leaf_of_residuals
    (hE6D : Up34Exc.Char2Hrat CFSG.Blueprint.Chevalley.Tag.E6 .twoD)
    (hE6E : Up34Exc.Char2Hrat CFSG.Blueprint.Chevalley.Tag.E6 .exc)
    (hE7D : Up34Exc.Char2Hrat CFSG.Blueprint.Chevalley.Tag.E7 .twoD)
    (hE7E : Up34Exc.Char2Hrat CFSG.Blueprint.Chevalley.Tag.E7 .exc)
    (hE8D : Up34Exc.Char2Hrat CFSG.Blueprint.Chevalley.Tag.E8 .twoD)
    (hE8E : Up34Exc.Char2Hrat CFSG.Blueprint.Chevalley.Tag.E8 .exc) : Up34Chev2Leaf := by
  have hE8i := Up34Chev2.up34C2Inn_E8_holds hE8D hE8E
  have hE6i := Up34Chev2.up34C2Inn_E6_holds Up34Exc.char2Hrat_inner_E6 Up34Exc.char2Hrat_suN_E6
    hE6D hE6E
  have hE6od := Up34Chev2.up34C2OutDiag_E6_holds Up34Exc.char2Hrat_inner_E6
    Up34Exc.char2Hrat_suN_E6 hE6D hE6E
  have hTE6i := Up34Chev2.up34C2Inn_TwE6_holds Up34Exc.char2Hrat_inner_E6
    Up34Exc.char2Hrat_suN_E6 hE6D hE6E
  have hTE6od := Up34Chev2.up34C2OutDiag_TwE6_holds Up34Exc.char2Hrat_inner_E6
    Up34Exc.char2Hrat_suN_E6 hE6D hE6E
  have hE7i := Up34Chev2.up34C2Inn_E7_holds hE7D hE7E
  refine up34Chev2Leaf_of_cover
    (F := fun d => FamA1 d ∨ FamA2 d ∨ FamAHigh d ∨ FamTwA2 d ∨ FamTwAHigh d ∨ FamB d ∨ FamD4 d ∨
      FamDHigh d ∨ FamTwD d ∨ FamE6 d ∨ FamTwE6 d ∨ FamE7 d ∨ FamE8 d ∨ FamF4 d ∨ FamG2 d ∨
      FamTriD4 d ∨ FamSz d ∨ FamReeF4 d ∨ FamTits d) (fun d hc => famCover d hc) ?_
  refine up34C2_l2.union ?_
  refine (Up34Chev2At.of_inn_out up34C2Inn_a2 (up34C2Out_a2_of_diag up34C2OutDiag_a2)).union ?_
  refine (Up34Chev2At.of_inn_out Up34Chev2.up34C2Inn_AHigh_holds
    (up34C2Out_aHigh_of_diag Up34Chev2.up34C2OutDiag_AHigh_holds)).union ?_
  refine (Up34Chev2At.of_inn_out up34C2Inn_twA2
    (up34C2Out_twA2_of_diag up34C2OutDiag_twA2)).union ?_
  refine (Up34Chev2At.of_inn_out Up34Chev2.up34C2Inn_TwAHigh_holds
    (up34C2Out_twAHigh_of_diag Up34Chev2.up34C2OutDiag_TwAHigh_holds)).union ?_
  refine (Up34Chev2At.of_inn_out up34C2Inn_B_holds up34C2Out_B).union ?_
  refine (Up34Chev2At.of_inn_out up34C2Inn_D4_holds up34C2Out_d4).union ?_
  refine (Up34Chev2At.of_inn_out up34C2Inn_DHigh_holds up34C2Out_dHigh).union ?_
  refine (Up34Chev2At.of_inn_out up34C2Inn_TwD_holds up34C2Out_twD).union ?_
  refine (Up34Chev2At.of_inn_out hE6i (up34C2Out_e6_of_diag hE6od)).union ?_
  refine (Up34Chev2At.of_inn_out hTE6i (up34C2Out_twE6_of_diag hTE6od)).union ?_
  refine (Up34Chev2At.of_inn_out hE7i up34C2Out_e7).union ?_
  refine (Up34Chev2At.of_inn_out hE8i up34C2Out_e8).union ?_
  refine (Up34Chev2At.of_inn_out Up34Chev2.up34C2Inn_F4_holds up34C2Out_f4).union ?_
  refine (Up34Chev2At.of_inn_out up34C2Inn_g2 up34C2Out_g2).union ?_
  refine (Up34Chev2At.of_inn_out up34C2Inn_triD4 up34C2Out_triD4).union ?_
  refine up34C2_sz.union ?_
  exact (Up34Chev2At.of_inn_out up34C2Inn_reeF4 up34C2Out_reeF4).union up34C2_tits

end CFSG.HardMathSupport.Dickson.Sec6
