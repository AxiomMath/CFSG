module

public import CFSG.Certificates.Kernel.Th.S.SeedS
public import CFSG.Certificates.Kernel.Th.Gen.Wrap
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.KC.Th.Gen

structure OrdersData where
  ThB_MD : Nat
  ThB_ND : Nat
  ThB_SUM : Nat
  ThK1_nLive : Nat
  ThK3_nLive : Nat
  ThS_Bi : Nat
  ThS_ONE : Nat
  ThS_RBf : Nat → Nat
  ThS_c : Nat
  ThS_dg : Nat
  ThS_n2 : Nat
  ThS_n3 : Nat
  ThS_n5 : Nat
  ThS_n7 : Nat
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

@[expose] noncomputable def ordersChk (D : OrdersData) : Bool :=
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (eqN (CFSG.KC.Th.BigS.runSlp D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.cs0 3) D.sf0)
  (CFSG.KC.Th.BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.SeedS.decOK D.ThSeed_SA D.ThSeed_LA)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.SeedS.decOK D.ThSeed_SB D.ThSeed_LB)
  (CFSG.KC.Th.SeedS.packOK D.ThSeed_SF CFSG.KC.Th.SeedS.fcRowsList))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA D.ThSeed_SA) D.ThS_ONE)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SB D.ThSeed_SB) D.ThSeed_SB) D.ThS_ONE)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.trB D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThSeed_SA) D.ThSeed_SF) D.ThSeed_SA) D.ThSeed_SF)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.trB D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThSeed_SB) D.ThSeed_SF) D.ThSeed_SB) D.ThSeed_SF)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBf 1) D.ThSeed_SA)
  (CFSG.KC.Th.Gen.eqN (D.ThS_RBf 2) D.ThSeed_SB)))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN D.ThS_w1 327208660843949311569856638931134950366718123578765707520623978699011294545)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN D.ThS_w2 53118203310247861616881865655955129280624587562044029180903589568007838922)
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThS_RBf 2) D.ThS_Bi) D.ThS_ONE)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.primeOrder D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThS_RBf 1) (D.ThS_RBf 2) D.ThS_Bi 294344331554 21) 13 5)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.primeOrder D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThS_RBf 1) (D.ThS_RBf 2) D.ThS_Bi 149845545878689 25) 31 5)
  (CFSG.KC.Th.BigS.primeOrder D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThS_RBf 1) (D.ThS_RBf 2)) 19 5))))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.BigS.primeOrder D.ThS_c D.ThS_rm D.ThS_ONE (D.ThS_RBf 1) 2 2)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.lcmN (CFSG.KC.Th.lcmN (CFSG.KC.Th.lcmN (CFSG.KC.Th.lcmN (CFSG.KC.Th.lcmN (CFSG.KC.Th.lcmN (CFSG.KC.Th.lcmN 1 (Nat.pow 2 D.ThS_n2)) (Nat.pow 3 D.ThS_n3)) (Nat.pow 5 D.ThS_n5)) (Nat.pow 7 D.ThS_n7)) 13) 19) 31) (Nat.mul (Nat.mul D.ThK1_nLive D.ThK3_nLive) D.ThB_SUM))
  (CFSG.KC.Th.primOK (CFSG.KC.Th.BigS.sizesOf D.ThB_MD (Nat.mul D.ThK1_nLive D.ThK3_nLive) 10) 10 D.ThB_SUM)))
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.Gen.eqN (Nat.mod (Nat.mul (Nat.mul D.ThK1_nLive D.ThK3_nLive) D.ThB_SUM) 19) 0)
  (CFSG.KC.Th.andB
  (CFSG.KC.Th.chkNe (Nat.mod (Nat.mul D.ThK1_nLive D.ThK3_nLive) 19) 0)
  (CFSG.KC.Th.Gen.eqN D.ThB_ND 11))))))

end CFSG.KC.Th.Gen

end
