module

public import CFSG.GH74.GLS.Bg.Pu5.L299Parts
public import CFSG.GH74.GLS.Bg.Pu5.L299M
public import CFSG.GH74.GLS.Bg.Pu5.L299Four
public import CFSG.GH74.GLS.Bg.Pu5.L299F1
public import CFSG.GH74.GLS.Bg.Pu5.L299F2
public import CFSG.GH74.GLS.Bg.Pu5.L297
public import CFSG.GH74.GLS.Bg.Pu5.L296
public import CFSG.GH74.GLS.Bg.Pu5.L295A
public import CFSG.GH74.GLS.Bg.Pu5.L295B
public import CFSG.GH74.GLS.Bg.Pu5.L293
public import CFSG.GH74.GLS.Bg.Pu5.LPTPLift
public import CFSG.GH74.GLS.Bg.Pu5.LPTPTransfer
public import CFSG.GH74.GLS.Bg.Pu5.BalB0
public import CFSG.GH74.GLS.Bg.Pu5.BalB1
public import CFSG.GH74.GLS.Bg.Pu5.BalASwap
public import CFSG.GH74.GLS.Bg.Iii2.II443d

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.IVK.Lifted

theorem b_pu5_G4_proved (h44 : II4_44) (hquat : II4_4_quat) (h2A7 : II4_2A7) (hAut : II4_Aut)
    (hrec : Bg.B_reciprocity) : Bg.B_pu5_G4 := by
  have hLP : L292LP := l292lp_of
  have hTP : L292TP := l292tp_of
  have h293 : L293 := l293_of hLP hTP h44 hquat
  have hP0 : P0S := p0_of hLP h44 hquat
  have hBal1 : Bal1S := bal1_of h44
  have hBL : BLS := bl_of h44
  have hDL : DiagLayerS := diagLayer_of
  have hBalSwap : BalSwapS := balSwap_of hBL hDL h44
  have h294a : L294a := l294a_of h44 hquat hBal1 h293
  have h294b : L294b := l294b_of h44 hquat hBalSwap h293
  have h295 : L295 :=
    l295_of_parts (l295a_of hP0 hDL bl0_of h293 hquat) (l295b_of hP0 bl0_of bl0s_of h294a h2A7 h44)
      (l295c_of hP0 hTP h293 h2A7 h44)
  have h296 : L296 := l296_of h295 h294b h293 hrec h2A7 h44 hquat
  have h297 : L297 := l297_of hquat h44 (ii4_43d_of h44 hAut) h296
  have hFour : L299FourS :=
    l299four_of h44 hquat h293 (l299f1_of h44 hquat hAut h296) (l299f2_of h44 hquat hAut h296 h294a)
  exact b_pu5_G4_of hquat h294a h296 h297
    (l299_of_parts (l299m_of h44 hquat h293 h296 hFour))

end CFSG.GH74.GLS.Bg.Pu5
