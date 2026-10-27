module

public import CFSG.Certificates.Kernel.Th.S.SeedS
public import CFSG.Certificates.Kernel.Th.Gen.Wrap
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.KC.Th.Gen

structure Sylow2Data where
  ThS_BL2 : Nat
  ThS_Ci2 : Nat
  ThS_Cm2 : Nat
  ThS_GL2 : Nat
  ThS_ONE : Nat
  ThS_PR2 : Nat
  ThS_PT2_0 : Nat → Nat
  ThS_PT2_1 : Nat → Nat
  ThS_PT2_10 : Nat → Nat
  ThS_PT2_11 : Nat → Nat
  ThS_PT2_2 : Nat → Nat
  ThS_PT2_3 : Nat → Nat
  ThS_PT2_4 : Nat → Nat
  ThS_PT2_5 : Nat → Nat
  ThS_PT2_6 : Nat → Nat
  ThS_PT2_7 : Nat → Nat
  ThS_PT2_8 : Nat → Nat
  ThS_PT2_9 : Nat → Nat
  ThS_RBf : Nat → Nat
  ThS_RBp2 : Nat → Nat
  ThS_c : Nat
  ThS_dg : Nat
  ThS_n2 : Nat
  ThS_nb2 : Nat
  ThS_rm : Nat
  ThS_tm0 : Nat
  ThS_tm1 : Nat
  ThS_tm2 : Nat
  ThS_tm3 : Nat
  ThS_tm4 : Nat
  ThS_tm5 : Nat
  ThS_tm6 : Nat
  ThS_tm7 : Nat
  ThS_up : Nat
  ThS_w1 : Nat
  ThS_w2 : Nat
  ThSeed_LA : List Char
  ThSeed_LB : List Char
  ThSeed_SA : Nat
  ThSeed_SB : Nat
  ThSeed_SF : Nat
  cs0 : List Nat
  sf0 : Nat
  cs1 : List Nat
  sf1 : Nat
  cs2 : List Nat
  sf2 : Nat
  cs3 : List Nat
  sf3 : Nat
  cs4 : List Nat
  sf4 : Nat
  cs5 : List Nat
  sf5 : Nat
  cs6 : List Nat
  sf6 : Nat
  cs7 : List Nat
  sf7 : Nat
  cs8 : List Nat
  sf8 : Nat
  cs9 : List Nat
  sf9 : Nat
  cs10 : List Nat
  sf10 : Nat
  cs11 : List Nat
  sf11 : Nat
  cs12 : List Nat
  sf12 : Nat
  cs13 : List Nat
  sf13 : Nat
  cs14 : List Nat
  sf14 : Nat
  cs15 : List Nat
  sf15 : Nat
  cs16 : List Nat
  sf16 : Nat
  cs17 : List Nat
  sf17 : Nat
  cs18 : List Nat
  sf18 : Nat
  cs19 : List Nat
  sf19 : Nat
  cs20 : List Nat
  sf20 : Nat
  cs21 : List Nat
  sf21 : Nat
  cs22 : List Nat
  sf22 : Nat
  cs23 : List Nat
  sf23 : Nat
  cs24 : List Nat
  sf24 : Nat
  cs25 : List Nat
  sf25 : Nat
  l0 : List Nat

@[expose] noncomputable def sylow2ChkGen (D : Sylow2Data) : Bool :=
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runSlp D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.cs0 3) D.sf0)
  (eqN (CFSG.KC.Th.BigS.runSlp D.ThS_RBp2 D.ThS_c D.ThS_rm D.ThS_ONE D.cs1 3) D.sf1))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp2 D.ThS_PT2_0 D.ThS_rm D.ThS_PR2 (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 0 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 5 5) D.cs2 2) D.sf2)
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT2_0 11 (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 5 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 0 5))) D.cs3 1) D.sf3)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp2 D.ThS_PT2_1 D.ThS_rm D.ThS_PR2 (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 10 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 15 5) D.cs4 2) D.sf4)
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT2_1 11 (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 15 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 10 5))) D.cs5 1) D.sf5))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp2 D.ThS_PT2_2 D.ThS_rm D.ThS_PR2 (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 20 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 25 5) D.cs6 2) D.sf6)
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT2_2 11 (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 25 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 20 5))) D.cs7 1) D.sf7))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp2 D.ThS_PT2_3 D.ThS_rm D.ThS_PR2 (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 30 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 35 5) D.cs8 2) D.sf8)
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT2_3 11 (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 35 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 30 5))) D.cs9 1) D.sf9))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp2 D.ThS_PT2_4 D.ThS_rm D.ThS_PR2 (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 40 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 45 5) D.cs10 2) D.sf10)
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT2_4 11 (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 45 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 40 5))) D.cs11 1) D.sf11)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp2 D.ThS_PT2_5 D.ThS_rm D.ThS_PR2 (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 50 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 55 5) D.cs12 2) D.sf12)
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT2_5 11 (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 55 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 50 5))) D.cs13 1) D.sf13))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp2 D.ThS_PT2_6 D.ThS_rm D.ThS_PR2 (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 60 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 65 5) D.cs14 2) D.sf14)
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT2_6 11 (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 65 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 60 5))) D.cs15 1) D.sf15)
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp2 D.ThS_PT2_7 D.ThS_rm D.ThS_PR2 (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 70 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 75 5) D.cs16 2) D.sf16))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT2_7 11 (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 75 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 70 5))) D.cs17 1) D.sf17)
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp2 D.ThS_PT2_8 D.ThS_rm D.ThS_PR2 (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 80 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 85 5) D.cs18 2) D.sf18))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT2_8 11 (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 85 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 80 5))) D.cs19 1) D.sf19)
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp2 D.ThS_PT2_9 D.ThS_rm D.ThS_PR2 (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 90 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 95 5) D.cs20 2) D.sf20)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT2_9 11 (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 95 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 90 5))) D.cs21 1) D.sf21)
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp2 D.ThS_PT2_10 D.ThS_rm D.ThS_PR2 (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 100 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 105 5) D.cs22 2) D.sf22))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT2_10 11 (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 105 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 100 5))) D.cs23 1) D.sf23)
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp2 D.ThS_PT2_11 D.ThS_rm D.ThS_PR2 (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 110 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 115 5) D.cs24 2) D.sf24)
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT2_11 11 (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 115 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 110 5))) D.cs25 1) D.sf25)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE)
  (CFSG.KC.Th.SeedS.decOK D.ThSeed_SA D.ThSeed_LA))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.SeedS.decOK D.ThSeed_SB D.ThSeed_LB)
  (CFSG.KC.Th.SeedS.packOK D.ThSeed_SF CFSG.KC.Th.SeedS.fcRowsList)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA D.ThSeed_SA) D.ThS_ONE)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SB D.ThSeed_SB) D.ThSeed_SB) D.ThS_ONE))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.trB D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThSeed_SA) D.ThSeed_SF) D.ThSeed_SA) D.ThSeed_SF)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.trB D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThSeed_SB) D.ThSeed_SF) D.ThSeed_SB) D.ThSeed_SF)
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBf 1) D.ThSeed_SA)))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBf 2) D.ThSeed_SB)
  (CFSG.KC.Th.Gen.eqN D.ThS_w1 327208660843949311569856638931134950366718123578765707520623978699011294545))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN D.ThS_w2 53118203310247861616881865655955129280624587562044029180903589568007838922)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.runMarked D.l0 9922901054488310019520462851) 356811923176489960380431918284599405230162057)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.allMarked D.ThS_PR2 15 174224571863520488467007772599902053335040)
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBp2 1) (D.ThS_RBf 1)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBp2 2) (D.ThS_RBf 2))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.regsIn D.ThS_PR2 D.ThS_n2 D.sf1)
  (CFSG.KC.Th.BigS.regsIn D.ThS_GL2 11 D.sf1)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThS_Cm2 D.ThS_Ci2) D.ThS_ONE)
  (CFSG.KC.Th.BigS.uniOK D.ThS_RBp2 D.ThS_c D.ThS_rm D.ThS_up D.ThS_dg D.ThS_Cm2 D.ThS_Ci2 D.ThS_GL2 11))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp2 D.ThS_rm D.ThS_PR2 (D.ThS_PT2_0 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 5 5) 15)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf3) (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 5 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 0 5))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp2 D.ThS_rm D.ThS_PR2 (D.ThS_PT2_1 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 15 5) 15)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf5) (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 15 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 10 5)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp2 D.ThS_rm D.ThS_PR2 (D.ThS_PT2_2 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 25 5) 15)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf7) (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 25 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 20 5))))
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp2 D.ThS_rm D.ThS_PR2 (D.ThS_PT2_3 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 35 5) 15))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf9) (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 35 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 30 5))))
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp2 D.ThS_rm D.ThS_PR2 (D.ThS_PT2_4 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 45 5) 15))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf11) (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 45 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 40 5))))
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp2 D.ThS_rm D.ThS_PR2 (D.ThS_PT2_5 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 55 5) 15)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf13) (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 55 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 50 5))))
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp2 D.ThS_rm D.ThS_PR2 (D.ThS_PT2_6 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 65 5) 15))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf15) (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 65 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 60 5))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp2 D.ThS_rm D.ThS_PR2 (D.ThS_PT2_7 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 75 5) 15)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf17) (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 75 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 70 5))))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp2 D.ThS_rm D.ThS_PR2 (D.ThS_PT2_8 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 85 5) 15)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf19) (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 85 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 80 5)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp2 D.ThS_rm D.ThS_PR2 (D.ThS_PT2_9 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 95 5) 15)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf21) (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 95 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 90 5))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp2 D.ThS_rm D.ThS_PR2 (D.ThS_PT2_10 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 105 5) 15)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf23) (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 105 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 100 5)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp2 D.ThS_rm D.ThS_PR2 (D.ThS_PT2_11 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 115 5) 15)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf25) (Nat.pow 2 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 115 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 110 5))))
  (CFSG.KC.Th.BigS.blocksOK D.ThS_BL2 D.ThS_nb2 D.ThS_n2))))))))

@[expose] noncomputable def sylow2Pins (D : Sylow2Data) : Bool :=
  CFSG.KC.Th.andB (decide (D.l0 = D.cs1))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN D.sf1 2048)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.ThS_GL2 106488374662378949350121827748335640)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.ThS_n2 15)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.ThS_nb2 12)
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf2 (Nat.succ (Nat.pow 2
    (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 5 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 0 5)))))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf4 (Nat.succ (Nat.pow 2
    (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 15 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 10 5)))))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf6 (Nat.succ (Nat.pow 2
    (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 25 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 20 5)))))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf8 (Nat.succ (Nat.pow 2
    (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 35 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 30 5)))))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf10 (Nat.succ (Nat.pow 2
    (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 45 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 40 5)))))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf12 (Nat.succ (Nat.pow 2
    (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 55 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 50 5)))))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf14 (Nat.succ (Nat.pow 2
    (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 65 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 60 5)))))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf16 (Nat.succ (Nat.pow 2
    (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 75 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 70 5)))))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf18 (Nat.succ (Nat.pow 2
    (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 85 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 80 5)))))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf20 (Nat.succ (Nat.pow 2
    (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 95 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 90 5)))))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf22 (Nat.succ (Nat.pow 2
    (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 105 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 100 5)))))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.eqN D.sf24 (Nat.succ (Nat.pow 2
    (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 115 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL2 110 5)))))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN (D.ThS_PT2_0 0) (Nat.pow 2 248))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN (D.ThS_PT2_1 0) (Nat.pow 2 248))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN (D.ThS_PT2_2 0) (Nat.pow 2 248))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN (D.ThS_PT2_3 0) (Nat.pow 2 248))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN (D.ThS_PT2_4 0) (Nat.pow 2 248))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN (D.ThS_PT2_5 0) (Nat.pow 2 248))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN (D.ThS_PT2_6 0) (Nat.pow 2 248))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN (D.ThS_PT2_7 0) (Nat.pow 2 248))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN (D.ThS_PT2_8 0) (Nat.pow 2 248))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN (D.ThS_PT2_9 0) (Nat.pow 2 248))
  (CFSG.KC.Th.andB (CFSG.KC.Th.Gen.ltN (D.ThS_PT2_10 0) (Nat.pow 2 248))
  (CFSG.KC.Th.Gen.ltN (D.ThS_PT2_11 0) (Nat.pow 2 248)))))))))))))))))))))))))))))

@[expose] noncomputable def sylow2Chk (D : Sylow2Data) : Bool :=
  CFSG.KC.Th.andB (sylow2ChkGen D) (sylow2Pins D)

end CFSG.KC.Th.Gen

end
