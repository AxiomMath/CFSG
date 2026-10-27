module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Frontier
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.C134L32CorrOf
public import CFSG.GH74.QTGen4.Leaves.ASCStatementsF4
public import CFSG.GH74.QTGen4.Leaves.Obl3313D12
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeV
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPair

public section

namespace CFSG.GH74.QTGen4.Leaves.S331

open CFSG.Quasithin CFSG.Quasithin.H13

theorem obl3_3_13D12_F4_holds
    : Obl3_3_13D12_F4 :=
  fun G _ _ => obl3_3_13D12_gen4 G (CFSG.GH74.QTGen4.Finite4.gen4 (G := G))

theorem theoremF618Cat_holds
    : F6.TheoremF618Cat :=
  F6.theoremF618Cat_of_residualRest (F6.f618ResidualRest_of_remaining
    (F6.f618ResidualRemaining_of_goldschmidt (F6.goldschmidtS3ListCat_of_charTwoLarge
      (F6.goldschmidtCharTwoLarge_of_pair F6.GoldAmLarge.goldschmidtCharTwoLargePair_holds.{0}))))

theorem c134L32Corr_F4_holds
    : C134L32Corr_F4 :=
  c134L32Corr_of_F4 fun G _ _ => ASCF4.as_C_1_34_corrGen4_holds G (CFSG.GH74.QTGen4.Finite4.gen4 (G := G))

theorem stmt3_3_1_F4_holds
    : Stmt3_3_1_F4 :=
  Frontier331.stmt3_3_1_of_frontier_F4 obl3_3_13D12_F4_holds ASCF4.as_C_1_32_F4_holds
    c134L32Corr_F4_holds ASCF4.asc27_F4_holds theoremF618Cat_holds

end CFSG.GH74.QTGen4.Leaves.S331
