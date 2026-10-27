module

public import CFSG.Certificates.Kernel.Th.S.SeedS
public import CFSG.Certificates.Kernel.Th.Gen.Wrap
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.KC.Th.Gen

structure Sylow3Data where
  ThS_BL3 : Nat
  ThS_GL3 : Nat
  ThS_ONE : Nat
  ThS_PR3 : Nat
  ThS_PT3_0 : Nat → Nat
  ThS_PT3_1 : Nat → Nat
  ThS_PT3_2 : Nat → Nat
  ThS_PT3_3 : Nat → Nat
  ThS_PW3 : Nat → Nat
  ThS_RBf : Nat → Nat
  ThS_RBp3 : Nat → Nat
  ThS_c : Nat
  ThS_dg : Nat
  ThS_n3 : Nat
  ThS_nb3 : Nat
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

@[expose] noncomputable def sylow3ChkGen (D : Sylow3Data) : Bool :=
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runSlp D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.cs0 3) D.sf0)
  (eqN (CFSG.KC.Th.BigS.runSlp D.ThS_RBp3 D.ThS_c D.ThS_rm D.ThS_ONE D.cs1 3) D.sf1))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runPc D.ThS_RBp3 D.ThS_PW3 D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_PR3 10 3 2 D.cs2 1) D.sf2)
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp3 D.ThS_PT3_0 D.ThS_rm D.ThS_PR3 (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 0 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 5 5) D.cs3 2) D.sf3)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT3_0 11 (Nat.pow 3 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 5 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 0 5))) D.cs4 1) D.sf4)
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp3 D.ThS_PT3_1 D.ThS_rm D.ThS_PR3 (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 10 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 15 5) D.cs5 2) D.sf5))
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT3_1 11 (Nat.pow 3 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 15 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 10 5))) D.cs6 1) D.sf6)
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp3 D.ThS_PT3_2 D.ThS_rm D.ThS_PR3 (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 20 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 25 5) D.cs7 2) D.sf7)
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT3_2 11 (Nat.pow 3 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 25 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 20 5))) D.cs8 1) D.sf8)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runTree D.ThS_RBp3 D.ThS_PT3_3 D.ThS_rm D.ThS_PR3 (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 30 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 35 5) D.cs9 2) D.sf9)
  (eqN (CFSG.KC.Th.DceS.runSorted D.ThS_PT3_3 11 (Nat.pow 3 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 35 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 30 5))) D.cs10 1) D.sf10))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.SeedS.decOK D.ThSeed_SA D.ThSeed_LA)
  (CFSG.KC.Th.SeedS.decOK D.ThSeed_SB D.ThSeed_LB))))
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
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBp3 1) (D.ThS_RBf 1))
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBp3 2) (D.ThS_RBf 2)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.pwOK D.ThS_RBp3 D.ThS_PW3 D.ThS_c D.ThS_rm D.ThS_PR3 D.sf5 3)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.gensPcOK D.ThS_GL3 3 D.ThS_PR3 D.ThS_n3 2080)
  (CFSG.KC.Th.BigS.regsIn D.ThS_PR3 D.ThS_n3 D.sf1)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.regsIn D.ThS_GL3 3 D.sf1)
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp3 D.ThS_rm D.ThS_PR3 (D.ThS_PT3_0 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 5 5) D.sf5))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf4) (Nat.pow 3 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 5 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 0 5))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp3 D.ThS_rm D.ThS_PR3 (D.ThS_PT3_1 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 15 5) D.sf5)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf6) (Nat.pow 3 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 15 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 D.sf5 5)))))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp3 D.ThS_rm D.ThS_PR3 (D.ThS_PT3_2 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 25 5) D.sf5)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf8) (Nat.pow 3 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 25 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 20 5)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.baseFixed D.ThS_RBp3 D.ThS_rm D.ThS_PR3 (D.ThS_PT3_3 0) (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 35 5) D.sf5)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.DceS.sortedCount D.sf10) (Nat.pow 3 (Nat.sub (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 35 5) (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 30 5))))
  (CFSG.KC.Th.BigS.blocksOK D.ThS_BL3 D.ThS_nb3 D.ThS_n3)))))))

@[expose] noncomputable def sylow3Pins (D : Sylow3Data) : Bool :=
  CFSG.KC.Th.andB (eqN D.ThS_n3 10)
  (CFSG.KC.Th.andB (eqN D.ThS_nb3 4)
  (CFSG.KC.Th.andB (eqN D.sf1 67)
  (CFSG.KC.Th.andB (eqN D.sf2 11)
  (CFSG.KC.Th.andB (eqN D.sf3 730)
  (CFSG.KC.Th.andB (eqN D.sf5 10)
  (CFSG.KC.Th.andB (eqN D.sf7 4)
  (CFSG.KC.Th.andB (eqN D.sf9 4)
  (CFSG.KC.Th.andB (eqN (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 0 5) 0)
  (CFSG.KC.Th.andB (eqN (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 5 5) 6)
  (CFSG.KC.Th.andB (eqN (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 10 5) 6)
  (CFSG.KC.Th.andB (eqN (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 15 5) 8)
  (CFSG.KC.Th.andB (eqN (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 20 5) 8)
  (CFSG.KC.Th.andB (eqN (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 25 5) 9)
  (CFSG.KC.Th.andB (eqN (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 30 5) 9)
  (CFSG.KC.Th.andB (eqN (CFSG.KC.Th.BigS.bitsN D.ThS_BL3 35 5) 10)
  (CFSG.KC.Th.andB (ltN (D.ThS_PT3_0 0) (Nat.pow 2 248))
  (CFSG.KC.Th.andB (ltN (D.ThS_PT3_1 0) (Nat.pow 2 248))
  (CFSG.KC.Th.andB (ltN (D.ThS_PT3_2 0) (Nat.pow 2 248))
  (ltN (D.ThS_PT3_3 0) (Nat.pow 2 248))))))))))))))))))))

@[expose] noncomputable def sylow3Chk (D : Sylow3Data) : Bool :=
  CFSG.KC.Th.andB (sylow3ChkGen D) (sylow3Pins D)

end CFSG.KC.Th.Gen

end
