module

public import CFSG.Certificates.Kernel.Th.S.SeedS
public import CFSG.Certificates.Kernel.Th.Gen.Wrap
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.KC.Th.Gen

structure Sylow5Data where
  ThS_BL5 : Nat
  ThS_GL5 : Nat
  ThS_ONE : Nat
  ThS_PR5 : Nat
  ThS_PT5_0 : Nat → Nat
  ThS_PT5_1 : Nat → Nat
  ThS_PT5_2 : Nat → Nat
  ThS_PW5 : Nat → Nat
  ThS_RBf : Nat → Nat
  ThS_RBp5 : Nat → Nat
  ThS_c : Nat
  ThS_dg : Nat
  ThS_n5 : Nat
  ThS_nb5 : Nat
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

@[expose] noncomputable def sylow5ChkGen (D : Sylow5Data) : Bool :=
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runSlp D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.cs0 3) D.sf0)
  (eqN (CFSG.KC.Th.BigS.runSlp D.ThS_RBp5 D.ThS_c D.ThS_rm D.ThS_ONE D.cs1 3) D.sf1))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runPc D.ThS_RBp5 D.ThS_PW5 D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_PR5 3 5 3 D.cs2 1) D.sf2)
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp5 D.ThS_PT5_0 D.ThS_rm D.ThS_PR5 (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 0 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 5 5) D.cs3 2) D.sf3)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT5_0 11 (Nat.pow 5 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 5 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 0 5))) D.cs4 1) D.sf4)
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp5 D.ThS_PT5_1 D.ThS_rm D.ThS_PR5 (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 10 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 15 5) D.cs5 2) D.sf5))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT5_1 11 (Nat.pow 5 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 15 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 10 5))) D.cs6 1) D.sf6)
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp5 D.ThS_PT5_2 D.ThS_rm D.ThS_PR5 (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 20 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 25 5) D.cs7 2) D.sf7))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT5_2 11 (Nat.pow 5 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 25 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 20 5))) D.cs8 1) D.sf8)
  (CFSG.KC.Th.BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.SeedS.decOK D.ThSeed_SA D.ThSeed_LA)
  (CFSG.KC.Th.SeedS.decOK D.ThSeed_SB D.ThSeed_LB)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.SeedS.packOK D.ThSeed_SF CFSG.KC.Th.SeedS.fcRowsList)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA D.ThSeed_SA) D.ThS_ONE))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SB D.ThSeed_SB) D.ThSeed_SB) D.ThS_ONE)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.trB D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThSeed_SA) D.ThSeed_SF) D.ThSeed_SA) D.ThSeed_SF)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.trB D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThSeed_SB) D.ThSeed_SF) D.ThSeed_SB) D.ThSeed_SF))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBf 1) D.ThSeed_SA)
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBf 2) D.ThSeed_SB))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN D.ThS_w1 327208660843949311569856638931134950366718123578765707520623978699011294545)
  (CFSG.KC.Th.Gen.eqN D.ThS_w2 53118203310247861616881865655955129280624587562044029180903589568007838922)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBp5 1) (D.ThS_RBf 1))
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBp5 2) (D.ThS_RBf 2)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.pwOK D.ThS_RBp5 D.ThS_PW5 D.ThS_c D.ThS_rm D.ThS_PR5 3 5)
  (CFSG.KC.Th.BigS.gensPcOK D.ThS_GL5 2 D.ThS_PR5 D.ThS_n5 32))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.regsIn D.ThS_PR5 D.ThS_n5 D.sf1)
  (CFSG.KC.Th.BigS.regsIn D.ThS_GL5 2 D.sf1))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp5 D.ThS_rm D.ThS_PR5 (D.ThS_PT5_0 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 5 5) 3)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf4) (Nat.pow 5 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 5 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 0 5))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp5 D.ThS_rm D.ThS_PR5 (D.ThS_PT5_1 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 15 5) 3)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf6) (Nat.pow 5 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 15 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 10 5)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp5 D.ThS_rm D.ThS_PR5 (D.ThS_PT5_2 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 25 5) 3)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf8) (Nat.pow 5 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 25 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 20 5))))
  (CFSG.KC.Th.BigS.blocksOK D.ThS_BL5 D.ThS_nb5 D.ThS_n5)))))))

@[expose] noncomputable def sylow5Pins (D : Sylow5Data) : Bool :=
  CFSG.KC.Th.andB (eqN D.ThS_n5 3)
  (CFSG.KC.Th.andB (eqN D.ThS_nb5 3)
  (CFSG.KC.Th.andB (eqN D.sf1 39)
  (CFSG.KC.Th.andB (eqN D.sf2 4)
  (CFSG.KC.Th.andB (eqN D.sf3 6)
  (CFSG.KC.Th.andB (eqN D.sf5 6)
  (CFSG.KC.Th.andB (eqN D.sf7 6)
  (CFSG.KC.Th.andB (eqN (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 0 5) 0)
  (CFSG.KC.Th.andB (eqN (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 5 5) 1)
  (CFSG.KC.Th.andB (eqN (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 10 5) 1)
  (CFSG.KC.Th.andB (eqN (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 15 5) 2)
  (CFSG.KC.Th.andB (eqN (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 20 5) 2)
  (CFSG.KC.Th.andB (eqN (CFSG.KC.Th.BigS.bitsN D.ThS_BL5 25 5) 3)
  (CFSG.KC.Th.andB (ltN (D.ThS_PT5_0 0) (Nat.pow 2 248))
  (CFSG.KC.Th.andB (ltN (D.ThS_PT5_1 0) (Nat.pow 2 248))
  (ltN (D.ThS_PT5_2 0) (Nat.pow 2 248))))))))))))))))

@[expose] noncomputable def sylow5Chk (D : Sylow5Data) : Bool :=
  CFSG.KC.Th.andB (sylow5ChkGen D) (sylow5Pins D)

end CFSG.KC.Th.Gen

end
